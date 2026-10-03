/*
 * src/goap.c — FinalBuildSystems goal-oriented action planner. Implements
 * include/fbs/goap.h.
 *
 * Design owes its problem framing (atoms, actions with preconditions, effects
 * and a cost, a procedural-precondition hook, a node cap, replanning from the
 * current state) to Narratech's GOAP NPC, which is MIT upstream; its license
 * is vendored at third_party/narratech/ and no line of that plugin is
 * reproduced here. The model, the search and the schemas are ours. Every
 * defect found in that plugin's planner (labelled G-1 .. G-18) is designed
 * out:
 *
 *   G-1/G-3  node identity is (byte-exact state blob, depth), hashed FNV-1a 64
 *            with a memcmp fallback; the closed set is consulted and a state
 *            re-enters the open set at a given depth only with a strictly
 *            lower g, which is what makes the depth cap sound AND complete.
 *   G-2      binary heap: a pop removes exactly one node.
 *   G-4      fbs_goap_outcome distinguishes all six conclusions.
 *   G-5      no uninitialised fields; the whole block is zeroed at create.
 *   G-6/G-7  h = 0 (optimal by construction) or H_MAX_UNSAT, which is
 *            admissible; relaxation is standard A* against the recorded node.
 *   G-8      proc_pre == NULL means applicable.
 *   G-9      keys are compared bytewise.
 *   G-10/14  one allocation per object, freed by _destroy; no raw owning
 *            pointers, no globals, no static mutable state.
 *   G-11     int32 costs, range-checked at registration and on override, and
 *            every path sum checked against FBS_GOAP_COST_MAX.
 *   G-12     per-agent costs are request.cost_override; the domain is const
 *            while planning.
 *   G-15     plans are written in execution order.
 *   G-16     fbs_goap_plan_validate answers "is my plan still good?".
 *   G-18     dense int32 slots; zero allocation during search.
 *
 * C99. Standard library only (no libm, no floating point anywhere).
 */

#include "fbs/goap.h"

#include <stdlib.h>
#include <string.h>

/* ------------------------------------------------------------------------- */
/* Limits, small helpers                                                     */
/* ------------------------------------------------------------------------- */

#define FBS_GOAP_SCHEMA_VERSION 1u

#define FBS_GOAP_MAX_ATOMS_LIMIT 4096u
#define FBS_GOAP_MAX_ACTIONS_LIMIT 4096u
#define FBS_GOAP_MAX_ROWS_LIMIT 1048576u  /* 1 << 20 */
#define FBS_GOAP_MAX_KEY_BYTES_LIMIT 67108864u /* 1 << 26 */
#define FBS_GOAP_MAX_KEY_LEN 255u
#define FBS_GOAP_MAX_NODES_LIMIT 4194304u /* 1 << 22 */
#define FBS_GOAP_MAX_DEPTH_LIMIT 65535u

/* Domain blob ("FBSG" version 1) header and record sizes. */
#define FBS_GOAP_HEADER_BYTES 28u
#define FBS_GOAP_ATOM_BYTES 20u
#define FBS_GOAP_ACTION_BYTES 20u
#define FBS_GOAP_ACTION_EFF_BYTES 8u
#define FBS_GOAP_ROW_BYTES 8u

#define FBS_GOAP_BLOCK_ALIGN 8u

#define FBS_GOAP_NODE_NONE 0xFFFFFFFFu

static size_t fbs_align_up(size_t v) {
  return (v + (FBS_GOAP_BLOCK_ALIGN - 1u)) & ~(size_t)(FBS_GOAP_BLOCK_ALIGN - 1u);
}

static int fbs_is_cmp(int c) {
  return c == FBS_GOAP_EQ || c == FBS_GOAP_NE || c == FBS_GOAP_LT || c == FBS_GOAP_LE ||
         c == FBS_GOAP_GT || c == FBS_GOAP_GE;
}

static int fbs_is_op(int o) { return o == FBS_GOAP_SET || o == FBS_GOAP_ADD; }

static int fbs_is_heuristic(int h) { return h == FBS_GOAP_H_ZERO || h == FBS_GOAP_H_MAX_UNSAT; }

static int fbs_cost_ok(fbs_goap_cost c) { return c >= 0 && c <= FBS_GOAP_COST_MAX; }

/* Saturating add of two costs in [0, COST_MAX]; used for f = g + h only, where
 * saturation cannot hide a real plan cost (path sums are checked separately). */
static fbs_goap_cost fbs_cost_sat_add(fbs_goap_cost a, fbs_goap_cost b) {
  if (a > FBS_GOAP_COST_MAX - b) return FBS_GOAP_COST_MAX;
  return (fbs_goap_cost)(a + b);
}

static void *fbs_goap_default_alloc(void *user, size_t bytes) {
  (void)user;
  return malloc(bytes);
}

static void fbs_goap_default_free(void *user, void *ptr) {
  (void)user;
  free(ptr);
}

static uint64_t fbs_fnv1a64(const void *p, size_t n) {
  const unsigned char *b = (const unsigned char *)p;
  uint64_t h = 14695981039346656037ULL;
  size_t i;
  for (i = 0; i < n; ++i) {
    h ^= (uint64_t)b[i];
    h *= 1099511628211ULL;
  }
  return h;
}

static unsigned fbs_fnv1a32(const char *key, size_t len) {
  unsigned h = 2166136261u;
  size_t i;
  for (i = 0; i < len; ++i) {
    h ^= (unsigned)(unsigned char)key[i];
    h *= 16777619u;
  }
  return h;
}

static unsigned fbs_pow2_at_least(unsigned need) {
  unsigned cap = 8u;
  while (cap < need) cap <<= 1;
  return cap;
}

/* ------------------------------------------------------------------------- */
/* Internal representation                                                   */
/* ------------------------------------------------------------------------- */

typedef struct fbs_goap_atom_rec {
  unsigned key_off;
  unsigned key_len;
  int32_t min_value;
  int32_t max_value;
  int32_t default_value;
  fbs_goap_cost cheapest; /* seal: min base cost over actions with an effect here */
} fbs_goap_atom_rec;

typedef struct fbs_goap_action_rec {
  unsigned key_off;
  unsigned key_len;
  fbs_goap_cost cost;
  unsigned cond_off; /* valid after seal */
  unsigned cond_count;
  unsigned eff_off; /* valid after seal */
  unsigned eff_count;
} fbs_goap_action_rec;

/* One precondition or effect row. `kind` is an fbs_goap_cmp for conditions and
 * an fbs_goap_effect_op for effects. Rows live in one array per kind in
 * registration order until seal, which sorts them by (action, atom, kind,
 * value) and hands each action a contiguous slice. */
typedef struct fbs_goap_row {
  uint16_t action;
  uint16_t atom;
  uint8_t kind;
  uint8_t pad;
  int32_t value;
} fbs_goap_row;

struct fbs_goap_domain {
  fbs_goap_allocator alloc;
  size_t block_size;
  unsigned max_atoms;
  unsigned max_actions;
  unsigned max_conditions;
  unsigned max_effects;
  unsigned max_key_bytes;
  unsigned atom_hash_cap;   /* power of two, >= 2 * max_atoms */
  unsigned action_hash_cap; /* power of two, >= 2 * max_actions */
  unsigned atom_count;
  unsigned action_count;
  unsigned cond_count;
  unsigned eff_count;
  unsigned key_top;
  int sealed;
  fbs_goap_atom_rec *atoms;
  fbs_goap_action_rec *actions;
  fbs_goap_row *conds;
  fbs_goap_row *effs;
  unsigned *atom_hash;   /* atom id + 1, 0 = empty */
  unsigned *action_hash; /* action id + 1, 0 = empty */
  char *keys;
};

/* The state blob: atom_count, the known bitmap, then one i32 value per atom
 * in atom id order. Unknown slots hold a canonical zero so identity is memcmp
 * and hashing is safe. */
struct fbs_goap_state {
  uint32_t atom_count;
  uint32_t data[1]; /* known bitmap words, then values; see the accessors */
};

static unsigned fbs_known_words(unsigned atom_count) { return (atom_count + 31u) / 32u; }

static size_t fbs_state_bytes(unsigned atom_count) {
  return (size_t)4u + (size_t)4u * fbs_known_words(atom_count) + (size_t)4u * atom_count;
}

static uint32_t *fbs_state_known(fbs_goap_state *s) { return s->data; }
static const uint32_t *fbs_state_known_c(const fbs_goap_state *s) { return s->data; }

static int32_t *fbs_state_values(fbs_goap_state *s, unsigned atom_count) {
  return (int32_t *)(void *)(s->data + fbs_known_words(atom_count));
}

static const int32_t *fbs_state_values_c(const fbs_goap_state *s, unsigned atom_count) {
  return (const int32_t *)(const void *)(s->data + fbs_known_words(atom_count));
}

static int fbs_slot_known(const fbs_goap_state *s, fbs_goap_atom a) {
  return (fbs_state_known_c(s)[a >> 5] >> (a & 31u)) & 1u ? 1 : 0;
}

static void fbs_slot_mark(fbs_goap_state *s, fbs_goap_atom a) {
  fbs_state_known(s)[a >> 5] |= (uint32_t)1u << (a & 31u);
}

static void fbs_slot_unmark(fbs_goap_state *s, fbs_goap_atom a) {
  fbs_state_known(s)[a >> 5] &= ~((uint32_t)1u << (a & 31u));
}

/* ------------------------------------------------------------------------- */
/* Status names, version, configs                                            */
/* ------------------------------------------------------------------------- */

const char *fbs_goap_status_name(int status) {
  switch (status) {
    case FBS_GOAP_OK: return "ok";
    case FBS_GOAP_E_INVALID: return "invalid";
    case FBS_GOAP_E_NOT_FOUND: return "not_found";
    case FBS_GOAP_E_EXISTS: return "exists";
    case FBS_GOAP_E_FULL: return "full";
    case FBS_GOAP_E_RANGE: return "range";
    case FBS_GOAP_E_SCHEMA: return "schema";
    case FBS_GOAP_E_TRUNCATED: return "truncated";
    case FBS_GOAP_E_SEALED: return "sealed";
    case FBS_GOAP_E_STATE: return "state";
    case FBS_GOAP_E_MEMORY: return "memory";
    default: return "unknown";
  }
}

unsigned fbs_goap_version(void) { return FBS_GOAP_VERSION; }

fbs_goap_config fbs_goap_config_default(void) {
  fbs_goap_config cfg;
  cfg.max_atoms = 64u;
  cfg.max_actions = 64u;
  cfg.max_conditions = 512u;
  cfg.max_effects = 512u;
  cfg.max_key_bytes = 4096u;
  return cfg;
}

fbs_goap_planner_config fbs_goap_planner_config_default(void) {
  fbs_goap_planner_config cfg;
  cfg.max_nodes = 4096u;
  cfg.max_depth = 64u;
  return cfg;
}

static int fbs_config_valid(const fbs_goap_config *cfg) {
  if (cfg->max_atoms < 1u || cfg->max_atoms > FBS_GOAP_MAX_ATOMS_LIMIT) return 0;
  if (cfg->max_actions < 1u || cfg->max_actions > FBS_GOAP_MAX_ACTIONS_LIMIT) return 0;
  if (cfg->max_conditions > FBS_GOAP_MAX_ROWS_LIMIT) return 0;
  if (cfg->max_effects > FBS_GOAP_MAX_ROWS_LIMIT) return 0;
  if (cfg->max_key_bytes < 1u || cfg->max_key_bytes > FBS_GOAP_MAX_KEY_BYTES_LIMIT) return 0;
  return 1;
}

static int fbs_planner_config_valid(const fbs_goap_planner_config *cfg) {
  if (cfg->max_nodes < 1u || cfg->max_nodes > FBS_GOAP_MAX_NODES_LIMIT) return 0;
  if (cfg->max_depth < 1u || cfg->max_depth > FBS_GOAP_MAX_DEPTH_LIMIT) return 0;
  return 1;
}

/* ------------------------------------------------------------------------- */
/* Key index (insert only: ids are never retired or reused)                  */
/* ------------------------------------------------------------------------- */

static void fbs_key_insert(unsigned *table, unsigned cap, const char *keys, const char *key,
                           size_t key_len, unsigned id) {
  unsigned mask = cap - 1u;
  unsigned i = fbs_fnv1a32(key, key_len) & mask;
  (void)keys;
  while (table[i] != 0u) i = (i + 1u) & mask;
  table[i] = id + 1u;
}

/* Generic lookup: `off` and `len` fetch the stored key of a candidate id. */
static unsigned fbs_key_find(const unsigned *table, unsigned cap, const char *keys,
                             const void *records, size_t record_bytes, size_t off_of_off,
                             size_t off_of_len, const char *key, size_t key_len) {
  unsigned mask = cap - 1u;
  unsigned i = fbs_fnv1a32(key, key_len) & mask;
  while (table[i] != 0u) {
    unsigned id = table[i] - 1u;
    const unsigned char *rec = (const unsigned char *)records + (size_t)id * record_bytes;
    unsigned koff, klen;
    memcpy(&koff, rec + off_of_off, sizeof koff);
    memcpy(&klen, rec + off_of_len, sizeof klen);
    if ((size_t)klen == key_len && memcmp(keys + koff, key, key_len) == 0) return id;
    i = (i + 1u) & mask;
  }
  return 0xFFFFFFFFu;
}

static unsigned fbs_atom_lookup(const fbs_goap_domain *d, const char *key, size_t key_len) {
  return fbs_key_find(d->atom_hash, d->atom_hash_cap, d->keys, d->atoms, sizeof(fbs_goap_atom_rec),
                      offsetof(fbs_goap_atom_rec, key_off), offsetof(fbs_goap_atom_rec, key_len), key,
                      key_len);
}

static unsigned fbs_action_lookup(const fbs_goap_domain *d, const char *key, size_t key_len) {
  return fbs_key_find(d->action_hash, d->action_hash_cap, d->keys, d->actions,
                      sizeof(fbs_goap_action_rec), offsetof(fbs_goap_action_rec, key_off),
                      offsetof(fbs_goap_action_rec, key_len), key, key_len);
}

/* ------------------------------------------------------------------------- */
/* Domain lifetime                                                           */
/* ------------------------------------------------------------------------- */

static size_t fbs_domain_layout(const fbs_goap_config *cfg, unsigned atom_hash_cap,
                                unsigned action_hash_cap, size_t *o_atoms, size_t *o_actions,
                                size_t *o_conds, size_t *o_effs, size_t *o_ahash, size_t *o_chash,
                                size_t *o_keys) {
  size_t off = fbs_align_up(sizeof(struct fbs_goap_domain));
  *o_atoms = off;
  off = fbs_align_up(off + (size_t)cfg->max_atoms * sizeof(fbs_goap_atom_rec));
  *o_actions = off;
  off = fbs_align_up(off + (size_t)cfg->max_actions * sizeof(fbs_goap_action_rec));
  *o_conds = off;
  off = fbs_align_up(off + (size_t)cfg->max_conditions * sizeof(fbs_goap_row));
  *o_effs = off;
  off = fbs_align_up(off + (size_t)cfg->max_effects * sizeof(fbs_goap_row));
  *o_ahash = off;
  off = fbs_align_up(off + (size_t)atom_hash_cap * sizeof(unsigned));
  *o_chash = off;
  off = fbs_align_up(off + (size_t)action_hash_cap * sizeof(unsigned));
  *o_keys = off;
  off = fbs_align_up(off + (size_t)cfg->max_key_bytes);
  return off;
}

static fbs_goap_status fbs_domain_alloc(const fbs_goap_config *cfg, const fbs_goap_allocator *alloc,
                                        fbs_goap_domain **out) {
  fbs_goap_allocator a;
  size_t o_atoms, o_actions, o_conds, o_effs, o_ahash, o_chash, o_keys, total;
  unsigned atom_hash_cap, action_hash_cap;
  unsigned char *block;
  fbs_goap_domain *d;

  if (alloc) {
    if (!alloc->alloc || !alloc->free) return FBS_GOAP_E_INVALID;
    a = *alloc;
  } else {
    a.alloc = fbs_goap_default_alloc;
    a.free = fbs_goap_default_free;
    a.user = NULL;
  }

  atom_hash_cap = fbs_pow2_at_least(cfg->max_atoms * 2u);
  action_hash_cap = fbs_pow2_at_least(cfg->max_actions * 2u);
  total = fbs_domain_layout(cfg, atom_hash_cap, action_hash_cap, &o_atoms, &o_actions, &o_conds,
                            &o_effs, &o_ahash, &o_chash, &o_keys);

  block = (unsigned char *)a.alloc(a.user, total);
  if (!block) return FBS_GOAP_E_MEMORY;
  memset(block, 0, total);

  d = (fbs_goap_domain *)(void *)block;
  d->alloc = a;
  d->block_size = total;
  d->max_atoms = cfg->max_atoms;
  d->max_actions = cfg->max_actions;
  d->max_conditions = cfg->max_conditions;
  d->max_effects = cfg->max_effects;
  d->max_key_bytes = cfg->max_key_bytes;
  d->atom_hash_cap = atom_hash_cap;
  d->action_hash_cap = action_hash_cap;
  d->atoms = (fbs_goap_atom_rec *)(void *)(block + o_atoms);
  d->actions = (fbs_goap_action_rec *)(void *)(block + o_actions);
  d->conds = (fbs_goap_row *)(void *)(block + o_conds);
  d->effs = (fbs_goap_row *)(void *)(block + o_effs);
  d->atom_hash = (unsigned *)(void *)(block + o_ahash);
  d->action_hash = (unsigned *)(void *)(block + o_chash);
  d->keys = (char *)(void *)(block + o_keys);

  *out = d;
  return FBS_GOAP_OK;
}

fbs_goap_status fbs_goap_domain_create(const fbs_goap_config *cfg, const fbs_goap_allocator *alloc,
                                       fbs_goap_domain **out) {
  fbs_goap_config c;
  fbs_goap_domain *d = NULL;
  fbs_goap_status st;

  if (!out) return FBS_GOAP_E_INVALID;
  c = cfg ? *cfg : fbs_goap_config_default();
  if (!fbs_config_valid(&c)) return FBS_GOAP_E_INVALID;

  st = fbs_domain_alloc(&c, alloc, &d);
  if (st != FBS_GOAP_OK) return st;
  *out = d;
  return FBS_GOAP_OK;
}

void fbs_goap_domain_destroy(fbs_goap_domain *d) {
  fbs_goap_allocator a;
  if (!d) return;
  a = d->alloc;
  a.free(a.user, d);
}

void fbs_goap_domain_clear(fbs_goap_domain *d) {
  if (!d) return;
  if (d->atom_count > 0u) memset(d->atoms, 0, (size_t)d->atom_count * sizeof(fbs_goap_atom_rec));
  if (d->action_count > 0u)
    memset(d->actions, 0, (size_t)d->action_count * sizeof(fbs_goap_action_rec));
  if (d->cond_count > 0u) memset(d->conds, 0, (size_t)d->cond_count * sizeof(fbs_goap_row));
  if (d->eff_count > 0u) memset(d->effs, 0, (size_t)d->eff_count * sizeof(fbs_goap_row));
  memset(d->atom_hash, 0, (size_t)d->atom_hash_cap * sizeof(unsigned));
  memset(d->action_hash, 0, (size_t)d->action_hash_cap * sizeof(unsigned));
  d->atom_count = 0u;
  d->action_count = 0u;
  d->cond_count = 0u;
  d->eff_count = 0u;
  d->key_top = 0u;
  d->sealed = 0;
}

size_t fbs_goap_domain_memory(const fbs_goap_domain *d) { return d ? d->block_size : (size_t)0; }

int fbs_goap_domain_is_sealed(const fbs_goap_domain *d) { return (d && d->sealed) ? 1 : 0; }

/* ------------------------------------------------------------------------- */
/* Atoms                                                                     */
/* ------------------------------------------------------------------------- */

fbs_goap_status fbs_goap_atom_add(fbs_goap_domain *d, const char *key, size_t key_len,
                                  int32_t min_value, int32_t max_value, int32_t default_value,
                                  fbs_goap_atom *out) {
  fbs_goap_atom_rec *rec;
  unsigned id;

  if (!d || !key || !out) return FBS_GOAP_E_INVALID;
  if (key_len == 0u || key_len > (size_t)FBS_GOAP_MAX_KEY_LEN) return FBS_GOAP_E_INVALID;
  if (d->sealed) return FBS_GOAP_E_SEALED;
  if (min_value > max_value) return FBS_GOAP_E_RANGE;
  if (default_value < min_value || default_value > max_value) return FBS_GOAP_E_RANGE;
  if (fbs_atom_lookup(d, key, key_len) != 0xFFFFFFFFu) return FBS_GOAP_E_EXISTS;
  if (d->atom_count >= d->max_atoms) return FBS_GOAP_E_FULL;
  if (key_len > (size_t)(d->max_key_bytes - d->key_top)) return FBS_GOAP_E_FULL;

  id = d->atom_count;
  rec = &d->atoms[id];
  rec->key_off = d->key_top;
  rec->key_len = (unsigned)key_len;
  rec->min_value = min_value;
  rec->max_value = max_value;
  rec->default_value = default_value;
  rec->cheapest = FBS_GOAP_COST_MAX;
  memcpy(d->keys + d->key_top, key, key_len);
  d->key_top += (unsigned)key_len;
  d->atom_count = id + 1u;
  fbs_key_insert(d->atom_hash, d->atom_hash_cap, d->keys, key, key_len, id);

  *out = (fbs_goap_atom)id;
  return FBS_GOAP_OK;
}

fbs_goap_status fbs_goap_atom_find(const fbs_goap_domain *d, const char *key, size_t key_len,
                                   fbs_goap_atom *out) {
  unsigned id;
  if (!d || !key || !out) return FBS_GOAP_E_INVALID;
  if (key_len == 0u || key_len > (size_t)FBS_GOAP_MAX_KEY_LEN) return FBS_GOAP_E_INVALID;
  id = fbs_atom_lookup(d, key, key_len);
  if (id == 0xFFFFFFFFu) return FBS_GOAP_E_NOT_FOUND;
  *out = (fbs_goap_atom)id;
  return FBS_GOAP_OK;
}

unsigned fbs_goap_atom_count(const fbs_goap_domain *d) { return d ? d->atom_count : 0u; }

static int fbs_atom_ok(const fbs_goap_domain *d, fbs_goap_atom a) {
  return (unsigned)a < d->atom_count;
}

static int fbs_action_ok(const fbs_goap_domain *d, fbs_goap_action act) {
  return (unsigned)act < d->action_count;
}

fbs_goap_status fbs_goap_atom_key(const fbs_goap_domain *d, fbs_goap_atom a, const char **out_key,
                                  size_t *out_len) {
  if (!d || !out_key || !out_len) return FBS_GOAP_E_INVALID;
  if (!fbs_atom_ok(d, a)) return FBS_GOAP_E_INVALID;
  *out_key = d->keys + d->atoms[a].key_off;
  *out_len = (size_t)d->atoms[a].key_len;
  return FBS_GOAP_OK;
}

fbs_goap_status fbs_goap_atom_range(const fbs_goap_domain *d, fbs_goap_atom a, int32_t *out_min,
                                    int32_t *out_max, int32_t *out_default) {
  if (!d || !out_min || !out_max || !out_default) return FBS_GOAP_E_INVALID;
  if (!fbs_atom_ok(d, a)) return FBS_GOAP_E_INVALID;
  *out_min = d->atoms[a].min_value;
  *out_max = d->atoms[a].max_value;
  *out_default = d->atoms[a].default_value;
  return FBS_GOAP_OK;
}

/* ------------------------------------------------------------------------- */
/* Actions and rows                                                          */
/* ------------------------------------------------------------------------- */

fbs_goap_status fbs_goap_action_add(fbs_goap_domain *d, const char *key, size_t key_len,
                                    fbs_goap_cost base_cost, fbs_goap_action *out) {
  fbs_goap_action_rec *rec;
  unsigned id;

  if (!d || !key || !out) return FBS_GOAP_E_INVALID;
  if (key_len == 0u || key_len > (size_t)FBS_GOAP_MAX_KEY_LEN) return FBS_GOAP_E_INVALID;
  if (d->sealed) return FBS_GOAP_E_SEALED;
  if (!fbs_cost_ok(base_cost)) return FBS_GOAP_E_RANGE;
  if (fbs_action_lookup(d, key, key_len) != 0xFFFFFFFFu) return FBS_GOAP_E_EXISTS;
  if (d->action_count >= d->max_actions) return FBS_GOAP_E_FULL;
  if (key_len > (size_t)(d->max_key_bytes - d->key_top)) return FBS_GOAP_E_FULL;

  id = d->action_count;
  rec = &d->actions[id];
  rec->key_off = d->key_top;
  rec->key_len = (unsigned)key_len;
  rec->cost = base_cost;
  rec->cond_off = 0u;
  rec->cond_count = 0u;
  rec->eff_off = 0u;
  rec->eff_count = 0u;
  memcpy(d->keys + d->key_top, key, key_len);
  d->key_top += (unsigned)key_len;
  d->action_count = id + 1u;
  fbs_key_insert(d->action_hash, d->action_hash_cap, d->keys, key, key_len, id);

  *out = (fbs_goap_action)id;
  return FBS_GOAP_OK;
}

fbs_goap_status fbs_goap_action_find(const fbs_goap_domain *d, const char *key, size_t key_len,
                                     fbs_goap_action *out) {
  unsigned id;
  if (!d || !key || !out) return FBS_GOAP_E_INVALID;
  if (key_len == 0u || key_len > (size_t)FBS_GOAP_MAX_KEY_LEN) return FBS_GOAP_E_INVALID;
  id = fbs_action_lookup(d, key, key_len);
  if (id == 0xFFFFFFFFu) return FBS_GOAP_E_NOT_FOUND;
  *out = (fbs_goap_action)id;
  return FBS_GOAP_OK;
}

unsigned fbs_goap_action_count(const fbs_goap_domain *d) { return d ? d->action_count : 0u; }

fbs_goap_status fbs_goap_action_key(const fbs_goap_domain *d, fbs_goap_action act,
                                    const char **out_key, size_t *out_len) {
  if (!d || !out_key || !out_len) return FBS_GOAP_E_INVALID;
  if (!fbs_action_ok(d, act)) return FBS_GOAP_E_INVALID;
  *out_key = d->keys + d->actions[act].key_off;
  *out_len = (size_t)d->actions[act].key_len;
  return FBS_GOAP_OK;
}

fbs_goap_status fbs_goap_action_cost(const fbs_goap_domain *d, fbs_goap_action act,
                                     fbs_goap_cost *out) {
  if (!d || !out) return FBS_GOAP_E_INVALID;
  if (!fbs_action_ok(d, act)) return FBS_GOAP_E_INVALID;
  *out = d->actions[act].cost;
  return FBS_GOAP_OK;
}

fbs_goap_status fbs_goap_action_pre(fbs_goap_domain *d, fbs_goap_action act, fbs_goap_atom a, int cmp,
                                    int32_t value) {
  unsigned i;
  fbs_goap_row *row;

  if (!d) return FBS_GOAP_E_INVALID;
  if (!fbs_action_ok(d, act) || !fbs_atom_ok(d, a) || !fbs_is_cmp(cmp)) return FBS_GOAP_E_INVALID;
  if (d->sealed) return FBS_GOAP_E_SEALED;
  /* Condition values are deliberately NOT range checked: "wood >= 11" against a
   * [0, 10] atom is a legitimate, provably unsatisfiable request (T-7). */
  for (i = 0u; i < d->cond_count; ++i) {
    const fbs_goap_row *r = &d->conds[i];
    if (r->action == (uint16_t)act && r->atom == (uint16_t)a && r->kind == (uint8_t)cmp &&
        r->value == value)
      return FBS_GOAP_E_EXISTS;
  }
  if (d->cond_count >= d->max_conditions) return FBS_GOAP_E_FULL;

  row = &d->conds[d->cond_count];
  row->action = (uint16_t)act;
  row->atom = (uint16_t)a;
  row->kind = (uint8_t)cmp;
  row->pad = 0u;
  row->value = value;
  d->cond_count += 1u;
  d->actions[act].cond_count += 1u;
  return FBS_GOAP_OK;
}

fbs_goap_status fbs_goap_action_effect(fbs_goap_domain *d, fbs_goap_action act, fbs_goap_atom a,
                                       int op, int32_t value) {
  unsigned i;
  fbs_goap_row *row;

  if (!d) return FBS_GOAP_E_INVALID;
  if (!fbs_action_ok(d, act) || !fbs_atom_ok(d, a) || !fbs_is_op(op)) return FBS_GOAP_E_INVALID;
  if (d->sealed) return FBS_GOAP_E_SEALED;
  if (op == FBS_GOAP_SET && (value < d->atoms[a].min_value || value > d->atoms[a].max_value))
    return FBS_GOAP_E_RANGE;
  /* At most one effect per (action, atom): a second one is E_EXISTS, whatever
   * its op, so effect application order can never matter. */
  for (i = 0u; i < d->eff_count; ++i) {
    const fbs_goap_row *r = &d->effs[i];
    if (r->action == (uint16_t)act && r->atom == (uint16_t)a) return FBS_GOAP_E_EXISTS;
  }
  if (d->eff_count >= d->max_effects) return FBS_GOAP_E_FULL;

  row = &d->effs[d->eff_count];
  row->action = (uint16_t)act;
  row->atom = (uint16_t)a;
  row->kind = (uint8_t)op;
  row->pad = 0u;
  row->value = value;
  d->eff_count += 1u;
  d->actions[act].eff_count += 1u;
  return FBS_GOAP_OK;
}

fbs_goap_status fbs_goap_action_conditions(const fbs_goap_domain *d, fbs_goap_action act,
                                           fbs_goap_cond *out, size_t cap, size_t *count) {
  unsigned i;
  size_t n = 0u;

  if (!d || !count) return FBS_GOAP_E_INVALID;
  if (!out && cap > 0u) return FBS_GOAP_E_INVALID;
  if (!fbs_action_ok(d, act)) return FBS_GOAP_E_INVALID;
  if ((size_t)d->actions[act].cond_count > cap) {
    *count = (size_t)d->actions[act].cond_count;
    return FBS_GOAP_E_TRUNCATED;
  }
  /* Sealed: the action owns a contiguous canonically sorted slice. Unsealed:
   * scan, which yields registration order (the documented pre-seal order). */
  for (i = 0u; i < d->cond_count; ++i) {
    const fbs_goap_row *r = &d->conds[i];
    if (r->action != (uint16_t)act) continue;
    out[n].atom = r->atom;
    out[n].cmp = r->kind;
    out[n].pad = 0u;
    out[n].value = r->value;
    ++n;
  }
  *count = n;
  return FBS_GOAP_OK;
}

fbs_goap_status fbs_goap_action_effects(const fbs_goap_domain *d, fbs_goap_action act,
                                        fbs_goap_effect *out, size_t cap, size_t *count) {
  unsigned i;
  size_t n = 0u;

  if (!d || !count) return FBS_GOAP_E_INVALID;
  if (!out && cap > 0u) return FBS_GOAP_E_INVALID;
  if (!fbs_action_ok(d, act)) return FBS_GOAP_E_INVALID;
  if ((size_t)d->actions[act].eff_count > cap) {
    *count = (size_t)d->actions[act].eff_count;
    return FBS_GOAP_E_TRUNCATED;
  }
  for (i = 0u; i < d->eff_count; ++i) {
    const fbs_goap_row *r = &d->effs[i];
    if (r->action != (uint16_t)act) continue;
    out[n].atom = r->atom;
    out[n].op = r->kind;
    out[n].pad = 0u;
    out[n].value = r->value;
    ++n;
  }
  *count = n;
  return FBS_GOAP_OK;
}

/* ------------------------------------------------------------------------- */
/* Seal: canonical row order, per-action slices, cheapest achiever costs      */
/* ------------------------------------------------------------------------- */

/* Total order on rows: (action, atom, kind, value). No two rows compare equal —
 * identical conditions are rejected at registration and an action has at most
 * one effect per atom — so the sorted result is unique and the algorithm used
 * to reach it is not observable. */
static int fbs_row_less(const fbs_goap_row *a, const fbs_goap_row *b) {
  if (a->action != b->action) return a->action < b->action;
  if (a->atom != b->atom) return a->atom < b->atom;
  if (a->kind != b->kind) return a->kind < b->kind;
  return a->value < b->value;
}

static void fbs_row_sift(fbs_goap_row *v, size_t n, size_t root) {
  for (;;) {
    size_t child = 2u * root + 1u;
    size_t big;
    fbs_goap_row tmp;
    if (child >= n) return;
    big = child;
    if (child + 1u < n && fbs_row_less(&v[child], &v[child + 1u])) big = child + 1u;
    if (!fbs_row_less(&v[root], &v[big])) return;
    tmp = v[root];
    v[root] = v[big];
    v[big] = tmp;
    root = big;
  }
}

/* Heapsort: in place (the domain is one allocation with no scratch) and O(n log n). */
static void fbs_row_sort(fbs_goap_row *v, size_t n) {
  size_t i;
  if (n < 2u) return;
  for (i = n / 2u; i-- > 0u;) fbs_row_sift(v, n, i);
  for (i = n; i-- > 1u;) {
    fbs_goap_row tmp = v[0];
    v[0] = v[i];
    v[i] = tmp;
    fbs_row_sift(v, i, 0u);
  }
}

fbs_goap_status fbs_goap_domain_seal(fbs_goap_domain *d) {
  unsigned i;
  unsigned off;

  if (!d) return FBS_GOAP_E_INVALID;
  if (d->sealed) return FBS_GOAP_OK; /* idempotent */

  fbs_row_sort(d->conds, (size_t)d->cond_count);
  fbs_row_sort(d->effs, (size_t)d->eff_count);

  off = 0u;
  for (i = 0u; i < d->action_count; ++i) {
    d->actions[i].cond_off = off;
    off += d->actions[i].cond_count;
  }
  off = 0u;
  for (i = 0u; i < d->action_count; ++i) {
    d->actions[i].eff_off = off;
    off += d->actions[i].eff_count;
  }

  /* Cheapest achiever per atom: the minimum base cost over the actions that
   * have an effect on it, FBS_GOAP_COST_MAX when no action can change it.
   * Any plan that has to satisfy a goal row on this atom must contain at least
   * one such action, so max over unsatisfied rows never overestimates. */
  for (i = 0u; i < d->atom_count; ++i) d->atoms[i].cheapest = FBS_GOAP_COST_MAX;
  for (i = 0u; i < d->eff_count; ++i) {
    fbs_goap_atom_rec *rec = &d->atoms[d->effs[i].atom];
    fbs_goap_cost c = d->actions[d->effs[i].action].cost;
    if (c < rec->cheapest) rec->cheapest = c;
  }

  d->sealed = 1;
  return FBS_GOAP_OK;
}

/* ------------------------------------------------------------------------- */
/* States                                                                    */
/* ------------------------------------------------------------------------- */

size_t fbs_goap_state_size(const fbs_goap_domain *d) {
  /* No status channel here: an unsealed or NULL domain reports 0, and every
   * state entry point that does have one reports E_STATE. */
  if (!d || !d->sealed) return 0u;
  return fbs_state_bytes(d->atom_count);
}

static fbs_goap_status fbs_state_check(const fbs_goap_domain *d, const fbs_goap_state *s) {
  if (!d->sealed) return FBS_GOAP_E_STATE;
  if (!s) return FBS_GOAP_E_INVALID;
  if (s->atom_count != (uint32_t)d->atom_count) return FBS_GOAP_E_INVALID;
  return FBS_GOAP_OK;
}

static fbs_goap_status fbs_state_prepare(const fbs_goap_domain *d, void *buf, size_t cap,
                                         fbs_goap_state **out, int defaults) {
  fbs_goap_state *s;
  size_t need;
  unsigned i;

  if (!d || !buf || !out) return FBS_GOAP_E_INVALID;
  if (!d->sealed) return FBS_GOAP_E_STATE;
  need = fbs_state_bytes(d->atom_count);
  /* No size output exists here, so a short or misaligned buffer is an argument
   * error (E_INVALID), not E_TRUNCATED: call fbs_goap_state_size first. */
  if (cap < need) return FBS_GOAP_E_INVALID;
  if (((size_t)(uintptr_t)buf & 3u) != 0u) return FBS_GOAP_E_INVALID;

  memset(buf, 0, need);
  s = (fbs_goap_state *)buf;
  s->atom_count = (uint32_t)d->atom_count;
  if (defaults) {
    int32_t *vals = fbs_state_values(s, d->atom_count);
    for (i = 0u; i < d->atom_count; ++i) {
      vals[i] = d->atoms[i].default_value;
      fbs_slot_mark(s, (fbs_goap_atom)i);
    }
  }
  *out = s;
  return FBS_GOAP_OK;
}

fbs_goap_status fbs_goap_state_init(const fbs_goap_domain *d, void *buf, size_t cap,
                                    fbs_goap_state **out) {
  return fbs_state_prepare(d, buf, cap, out, 0);
}

fbs_goap_status fbs_goap_state_init_defaults(const fbs_goap_domain *d, void *buf, size_t cap,
                                             fbs_goap_state **out) {
  return fbs_state_prepare(d, buf, cap, out, 1);
}

fbs_goap_status fbs_goap_state_copy(const fbs_goap_domain *d, fbs_goap_state *dst,
                                    const fbs_goap_state *src) {
  fbs_goap_status st;
  if (!d || !dst || !src) return FBS_GOAP_E_INVALID;
  st = fbs_state_check(d, dst);
  if (st != FBS_GOAP_OK) return st;
  st = fbs_state_check(d, src);
  if (st != FBS_GOAP_OK) return st;
  if (dst != src) memcpy(dst, src, fbs_state_bytes(d->atom_count));
  return FBS_GOAP_OK;
}

fbs_goap_status fbs_goap_state_set(const fbs_goap_domain *d, fbs_goap_state *s, fbs_goap_atom a,
                                   int32_t value) {
  fbs_goap_status st;
  if (!d || !s) return FBS_GOAP_E_INVALID;
  st = fbs_state_check(d, s);
  if (st != FBS_GOAP_OK) return st;
  if (!fbs_atom_ok(d, a)) return FBS_GOAP_E_INVALID;
  if (value < d->atoms[a].min_value || value > d->atoms[a].max_value) return FBS_GOAP_E_RANGE;
  fbs_state_values(s, d->atom_count)[a] = value;
  fbs_slot_mark(s, a);
  return FBS_GOAP_OK;
}

fbs_goap_status fbs_goap_state_unset(const fbs_goap_domain *d, fbs_goap_state *s, fbs_goap_atom a) {
  fbs_goap_status st;
  if (!d || !s) return FBS_GOAP_E_INVALID;
  st = fbs_state_check(d, s);
  if (st != FBS_GOAP_OK) return st;
  if (!fbs_atom_ok(d, a)) return FBS_GOAP_E_INVALID;
  /* The value word is forced back to the canonical zero, which is what keeps
   * fbs_goap_state_equal a plain memcmp. */
  fbs_state_values(s, d->atom_count)[a] = 0;
  fbs_slot_unmark(s, a);
  return FBS_GOAP_OK;
}

int fbs_goap_state_known(const fbs_goap_domain *d, const fbs_goap_state *s, fbs_goap_atom a) {
  fbs_goap_status st;
  if (!d || !s) return FBS_GOAP_E_INVALID;
  st = fbs_state_check(d, s);
  if (st != FBS_GOAP_OK) return (int)st;
  if (!fbs_atom_ok(d, a)) return FBS_GOAP_E_INVALID;
  return fbs_slot_known(s, a);
}

fbs_goap_status fbs_goap_state_get(const fbs_goap_domain *d, const fbs_goap_state *s, fbs_goap_atom a,
                                   int32_t *out) {
  fbs_goap_status st;
  if (!d || !s || !out) return FBS_GOAP_E_INVALID;
  st = fbs_state_check(d, s);
  if (st != FBS_GOAP_OK) return st;
  if (!fbs_atom_ok(d, a)) return FBS_GOAP_E_INVALID;
  if (!fbs_slot_known(s, a)) return FBS_GOAP_E_NOT_FOUND;
  *out = fbs_state_values_c(s, d->atom_count)[a];
  return FBS_GOAP_OK;
}

int fbs_goap_state_equal(const fbs_goap_domain *d, const fbs_goap_state *a, const fbs_goap_state *b) {
  fbs_goap_status st;
  if (!d || !a || !b) return FBS_GOAP_E_INVALID;
  st = fbs_state_check(d, a);
  if (st != FBS_GOAP_OK) return (int)st;
  st = fbs_state_check(d, b);
  if (st != FBS_GOAP_OK) return (int)st;
  return memcmp(a, b, fbs_state_bytes(d->atom_count)) == 0 ? 1 : 0;
}

static int fbs_cmp_holds(int cmp, int32_t have, int32_t want) {
  switch (cmp) {
    case FBS_GOAP_EQ: return have == want;
    case FBS_GOAP_NE: return have != want;
    case FBS_GOAP_LT: return have < want;
    case FBS_GOAP_LE: return have <= want;
    case FBS_GOAP_GT: return have > want;
    default: return have >= want; /* FBS_GOAP_GE */
  }
}

/* Caller has validated d, s and the rows. An unknown slot satisfies nothing. */
static int fbs_rows_hold(const fbs_goap_domain *d, const fbs_goap_state *s, const fbs_goap_cond *rows,
                         size_t n) {
  const int32_t *vals = fbs_state_values_c(s, d->atom_count);
  size_t i;
  for (i = 0u; i < n; ++i) {
    fbs_goap_atom a = rows[i].atom;
    if (!fbs_slot_known(s, a)) return 0;
    if (!fbs_cmp_holds((int)rows[i].cmp, vals[a], rows[i].value)) return 0;
  }
  return 1;
}

static int fbs_goal_rows_valid(const fbs_goap_domain *d, const fbs_goap_cond *rows, size_t n) {
  size_t i;
  for (i = 0u; i < n; ++i) {
    if (!fbs_atom_ok(d, rows[i].atom)) return 0;
    if (!fbs_is_cmp((int)rows[i].cmp)) return 0;
  }
  return 1;
}

int fbs_goap_state_satisfies(const fbs_goap_domain *d, const fbs_goap_state *s,
                             const fbs_goap_cond *goal, size_t goal_len) {
  fbs_goap_status st;
  if (!d || !s) return FBS_GOAP_E_INVALID;
  if (!goal && goal_len > 0u) return FBS_GOAP_E_INVALID;
  st = fbs_state_check(d, s);
  if (st != FBS_GOAP_OK) return (int)st;
  if (!fbs_goal_rows_valid(d, goal, goal_len)) return FBS_GOAP_E_INVALID;
  /* goal_len == 0 is vacuously satisfied; fbs_goap_plan separately requires
   * goal_len >= 1. */
  return fbs_rows_hold(d, s, goal, goal_len);
}

/* Applies the effect rows of `act` to `s`. Both SET and ADD leave the slot
 * KNOWN: an unknown slot reads as the canonical zero it always holds, so
 * "slot += value" on an unknown slot is clamp(0 + value) and the slot then has
 * a value. This is the only reading under which every effect is total. */
static void fbs_apply_effects(const fbs_goap_domain *d, fbs_goap_state *s, fbs_goap_action act) {
  int32_t *vals = fbs_state_values(s, d->atom_count);
  unsigned i;
  const fbs_goap_action_rec *rec = &d->actions[act];
  for (i = 0u; i < rec->eff_count; ++i) {
    const fbs_goap_row *r = &d->effs[rec->eff_off + i];
    const fbs_goap_atom_rec *at = &d->atoms[r->atom];
    if (r->kind == (uint8_t)FBS_GOAP_SET) {
      vals[r->atom] = r->value; /* range checked at registration */
    } else {
      /* 64-bit accumulation, then clamp: no int32 wrap is possible. */
      int64_t v = (int64_t)vals[r->atom] + (int64_t)r->value;
      if (v < (int64_t)at->min_value) v = (int64_t)at->min_value;
      if (v > (int64_t)at->max_value) v = (int64_t)at->max_value;
      vals[r->atom] = (int32_t)v;
    }
    fbs_slot_mark(s, (fbs_goap_atom)r->atom);
  }
}

fbs_goap_status fbs_goap_apply(const fbs_goap_domain *d, fbs_goap_state *s, fbs_goap_action act) {
  fbs_goap_status st;
  if (!d || !s) return FBS_GOAP_E_INVALID;
  st = fbs_state_check(d, s);
  if (st != FBS_GOAP_OK) return st;
  if (!fbs_action_ok(d, act)) return FBS_GOAP_E_INVALID;
  fbs_apply_effects(d, s, act);
  return FBS_GOAP_OK;
}

/* Caller has validated everything; sealed domains only (slices required). */
static int fbs_pre_holds(const fbs_goap_domain *d, const fbs_goap_state *s, fbs_goap_action act) {
  const fbs_goap_action_rec *rec = &d->actions[act];
  const int32_t *vals = fbs_state_values_c(s, d->atom_count);
  unsigned i;
  for (i = 0u; i < rec->cond_count; ++i) {
    const fbs_goap_row *r = &d->conds[rec->cond_off + i];
    if (!fbs_slot_known(s, (fbs_goap_atom)r->atom)) return 0;
    if (!fbs_cmp_holds((int)r->kind, vals[r->atom], r->value)) return 0;
  }
  return 1;
}

int fbs_goap_action_applicable(const fbs_goap_domain *d, const fbs_goap_state *s,
                               fbs_goap_action act) {
  fbs_goap_status st;
  if (!d || !s) return FBS_GOAP_E_INVALID;
  st = fbs_state_check(d, s);
  if (st != FBS_GOAP_OK) return (int)st;
  if (!fbs_action_ok(d, act)) return FBS_GOAP_E_INVALID;
  return fbs_pre_holds(d, s, act);
}

/* ------------------------------------------------------------------------- */
/* Planner                                                                   */
/* ------------------------------------------------------------------------- */

/* A search node is a (state, depth) pair, not a state: a state reached at a
 * different depth is a different node, so the depth cap cannot silently
 * discard the shorter, dearer route to a state that was first reached by a
 * cheaper, longer one. `depth` is part of the identity and is therefore never
 * rewritten; only g / parent / action move on a relaxation.
 *
 * Nodes with equal state bytes are chained through `next_same` off one hash
 * slot, so the generator can compare a candidate against every depth already
 * seen for that state and apply the dominance rule below. */
typedef struct fbs_goap_node {
  fbs_goap_cost g;
  fbs_goap_cost h;
  fbs_goap_cost f;      /* == sat_add(g, h) */
  unsigned parent;      /* node index, FBS_GOAP_NODE_NONE for the root */
  unsigned seq;         /* per-call insertion counter, 0 for the root */
  unsigned next_same;   /* next node with identical state bytes, or NODE_NONE */
  uint16_t action;      /* action that reached this node, ACTION_NONE for the root */
  uint16_t depth;
  unsigned char dead;   /* superseded by a no-deeper, no-dearer node */
  unsigned char pad[3];
} fbs_goap_node;

struct fbs_goap_planner {
  fbs_goap_allocator alloc;
  size_t block_size;
  const fbs_goap_domain *domain;
  unsigned max_nodes;
  unsigned max_depth;
  unsigned state_size; /* bytes per state blob */
  unsigned index_cap;  /* power of two, >= 2 * max_nodes */
  unsigned atom_count; /* the domain's atom count when the planner was created */
  unsigned char *states;
  fbs_goap_node *nodes;
  unsigned *heap;     /* heap position -> node index */
  unsigned *heap_pos; /* node index -> heap position, FBS_GOAP_NODE_NONE when not open */
  unsigned *index;    /* open addressing: node index + 1, 0 = empty */
  unsigned char *succ; /* one successor scratch state */
  fbs_goap_cost *cheapest; /* atom_count entries: override-aware achiever costs */
  unsigned node_count;
  unsigned heap_len;
};

static size_t fbs_planner_layout(unsigned max_nodes, unsigned state_size, unsigned index_cap,
                                 unsigned atom_count, size_t *o_states, size_t *o_nodes,
                                 size_t *o_heap, size_t *o_pos, size_t *o_index, size_t *o_succ,
                                 size_t *o_cheap) {
  size_t off = fbs_align_up(sizeof(struct fbs_goap_planner));
  *o_states = off;
  off = fbs_align_up(off + (size_t)max_nodes * state_size);
  *o_nodes = off;
  off = fbs_align_up(off + (size_t)max_nodes * sizeof(fbs_goap_node));
  *o_heap = off;
  off = fbs_align_up(off + (size_t)max_nodes * sizeof(unsigned));
  *o_pos = off;
  off = fbs_align_up(off + (size_t)max_nodes * sizeof(unsigned));
  *o_index = off;
  off = fbs_align_up(off + (size_t)index_cap * sizeof(unsigned));
  *o_succ = off;
  off = fbs_align_up(off + state_size);
  *o_cheap = off;
  off = fbs_align_up(off + (size_t)atom_count * sizeof(fbs_goap_cost));
  return off;
}

fbs_goap_status fbs_goap_planner_create(const fbs_goap_domain *d, const fbs_goap_planner_config *cfg,
                                        const fbs_goap_allocator *alloc, fbs_goap_planner **out) {
  fbs_goap_planner_config c;
  fbs_goap_allocator a;
  size_t o_states, o_nodes, o_heap, o_pos, o_index, o_succ, o_cheap, total;
  unsigned state_size, index_cap;
  unsigned char *block;
  fbs_goap_planner *p;

  if (!d || !out) return FBS_GOAP_E_INVALID;
  c = cfg ? *cfg : fbs_goap_planner_config_default();
  if (!fbs_planner_config_valid(&c)) return FBS_GOAP_E_INVALID;
  if (!d->sealed) return FBS_GOAP_E_STATE;

  if (alloc) {
    if (!alloc->alloc || !alloc->free) return FBS_GOAP_E_INVALID;
    a = *alloc;
  } else {
    a.alloc = fbs_goap_default_alloc;
    a.free = fbs_goap_default_free;
    a.user = NULL;
  }

  state_size = (unsigned)fbs_state_bytes(d->atom_count);
  index_cap = fbs_pow2_at_least(c.max_nodes * 2u);
  total = fbs_planner_layout(c.max_nodes, state_size, index_cap, d->atom_count, &o_states, &o_nodes,
                             &o_heap, &o_pos, &o_index, &o_succ, &o_cheap);

  block = (unsigned char *)a.alloc(a.user, total);
  if (!block) return FBS_GOAP_E_MEMORY;
  memset(block, 0, total);

  p = (fbs_goap_planner *)(void *)block;
  p->alloc = a;
  p->block_size = total;
  p->domain = d;
  p->max_nodes = c.max_nodes;
  p->max_depth = c.max_depth;
  p->state_size = state_size;
  p->index_cap = index_cap;
  p->atom_count = d->atom_count;
  p->states = block + o_states;
  p->nodes = (fbs_goap_node *)(void *)(block + o_nodes);
  p->heap = (unsigned *)(void *)(block + o_heap);
  p->heap_pos = (unsigned *)(void *)(block + o_pos);
  p->index = (unsigned *)(void *)(block + o_index);
  p->succ = block + o_succ;
  p->cheapest = (fbs_goap_cost *)(void *)(block + o_cheap);
  p->node_count = 0u;
  p->heap_len = 0u;

  *out = p;
  return FBS_GOAP_OK;
}

void fbs_goap_planner_destroy(fbs_goap_planner *p) {
  fbs_goap_allocator a;
  if (!p) return;
  a = p->alloc;
  a.free(a.user, p);
}

size_t fbs_goap_planner_memory(const fbs_goap_planner *p) { return p ? p->block_size : (size_t)0; }

static fbs_goap_state *fbs_node_state(fbs_goap_planner *p, unsigned node) {
  return (fbs_goap_state *)(void *)(p->states + (size_t)node * p->state_size);
}

/* Total order: f ascending, then g DESCENDING (prefer the more progressed node
 * among equal f), then insertion sequence ascending. No two distinct nodes
 * compare equal, so the pop order is fully determined. */
static int fbs_node_before(const fbs_goap_planner *p, unsigned x, unsigned y) {
  const fbs_goap_node *a = &p->nodes[x];
  const fbs_goap_node *b = &p->nodes[y];
  if (a->f != b->f) return a->f < b->f;
  if (a->g != b->g) return a->g > b->g;
  return a->seq < b->seq;
}

static void fbs_heap_sift_up(fbs_goap_planner *p, unsigned pos) {
  unsigned node = p->heap[pos];
  while (pos > 0u) {
    unsigned parent = (pos - 1u) / 2u;
    if (!fbs_node_before(p, node, p->heap[parent])) break;
    p->heap[pos] = p->heap[parent];
    p->heap_pos[p->heap[pos]] = pos;
    pos = parent;
  }
  p->heap[pos] = node;
  p->heap_pos[node] = pos;
}

static void fbs_heap_sift_down(fbs_goap_planner *p, unsigned pos) {
  unsigned node = p->heap[pos];
  for (;;) {
    unsigned child = 2u * pos + 1u;
    if (child >= p->heap_len) break;
    if (child + 1u < p->heap_len && fbs_node_before(p, p->heap[child + 1u], p->heap[child]))
      child += 1u;
    if (!fbs_node_before(p, p->heap[child], node)) break;
    p->heap[pos] = p->heap[child];
    p->heap_pos[p->heap[pos]] = pos;
    pos = child;
  }
  p->heap[pos] = node;
  p->heap_pos[node] = pos;
}

static void fbs_heap_push(fbs_goap_planner *p, unsigned node) {
  p->heap[p->heap_len] = node;
  p->heap_pos[node] = p->heap_len;
  p->heap_len += 1u;
  fbs_heap_sift_up(p, p->heap_len - 1u);
}

static unsigned fbs_heap_pop(fbs_goap_planner *p) {
  unsigned top = p->heap[0];
  p->heap_pos[top] = FBS_GOAP_NODE_NONE;
  p->heap_len -= 1u;
  if (p->heap_len > 0u) {
    p->heap[0] = p->heap[p->heap_len];
    p->heap_pos[p->heap[0]] = 0u;
    fbs_heap_sift_down(p, 0u);
  }
  return top;
}

/* State index: FNV-1a 64 of the state bytes with a memcmp check on collision.
 * One slot per distinct state; the slot holds the head of that state's chain of
 * (state, depth) nodes. Returns the slot holding the chain for `state`, or the
 * empty slot where that chain would start. The table is sized 2 * max_nodes and
 * holds at most max_nodes chains, so an empty slot always exists. */
static unsigned fbs_index_slot(fbs_goap_planner *p, const void *state) {
  unsigned mask = p->index_cap - 1u;
  unsigned i = (unsigned)(fbs_fnv1a64(state, p->state_size) & (uint64_t)mask);
  while (p->index[i] != 0u) {
    unsigned head = p->index[i] - 1u;
    if (memcmp(p->states + (size_t)head * p->state_size, state, p->state_size) == 0) return i;
    i = (i + 1u) & mask;
  }
  return i;
}

static unsigned fbs_index_head(const fbs_goap_planner *p, unsigned slot) {
  return p->index[slot] ? p->index[slot] - 1u : FBS_GOAP_NODE_NONE;
}

/* After `m` entered the chain (or got cheaper), every other live node of the
 * same state that is no shallower and no cheaper is dominated: any plan that
 * could be built from it can be built from `m` no longer and no dearer. Mark
 * those dead so a pop skips them. This is what keeps the (state, depth) space
 * from degenerating — a self-loop successor, for one, is always dominated by
 * its own parent, so idle actions can never inflate the frontier. */
static void fbs_index_prune(fbs_goap_planner *p, unsigned slot, unsigned m) {
  unsigned n;
  for (n = fbs_index_head(p, slot); n != FBS_GOAP_NODE_NONE; n = p->nodes[n].next_same) {
    if (n == m || p->nodes[n].dead) continue;
    if (p->nodes[n].depth >= p->nodes[m].depth && p->nodes[n].g >= p->nodes[m].g)
      p->nodes[n].dead = 1u;
  }
}

/* h for a state. H_ZERO is 0; H_MAX_UNSAT is the maximum, over the goal rows
 * the state does not satisfy, of that atom's cheapest achiever cost. */
static fbs_goap_cost fbs_heuristic(fbs_goap_planner *p, const fbs_goap_state *s, int heuristic,
                                   const fbs_goap_cond *goal, size_t goal_len) {
  const fbs_goap_domain *d = p->domain;
  const int32_t *vals;
  fbs_goap_cost best = 0;
  size_t i;

  if (heuristic == FBS_GOAP_H_ZERO) return 0;
  vals = fbs_state_values_c(s, d->atom_count);
  for (i = 0u; i < goal_len; ++i) {
    fbs_goap_atom a = goal[i].atom;
    fbs_goap_cost c;
    if (fbs_slot_known(s, a) && fbs_cmp_holds((int)goal[i].cmp, vals[a], goal[i].value)) continue;
    c = p->cheapest[a];
    if (c > best) best = c;
  }
  return best;
}

fbs_goap_status fbs_goap_plan(fbs_goap_planner *p, const fbs_goap_request *req,
                              fbs_goap_action *out_plan, size_t plan_cap, fbs_goap_result *out) {
  const fbs_goap_domain *d;
  fbs_goap_result res;
  unsigned cap_nodes, cap_depth;
  unsigned root, found = FBS_GOAP_NODE_NONE;
  unsigned next_seq = 1u;
  int outcome = FBS_GOAP_UNSOLVABLE;
  int depth_capped = 0;
  int stop = 0;
  unsigned i;

  if (!p || !req || !out) return FBS_GOAP_E_INVALID;
  if (!out_plan && plan_cap > 0u) return FBS_GOAP_E_INVALID;
  d = p->domain;
  if (!d->sealed) return FBS_GOAP_E_STATE;
  if (!req->start || !req->goal || req->goal_len == 0u) return FBS_GOAP_E_INVALID;
  if (!fbs_is_heuristic(req->heuristic)) return FBS_GOAP_E_INVALID;
  if (req->max_nodes > p->max_nodes) return FBS_GOAP_E_INVALID;
  if (req->max_depth > FBS_GOAP_MAX_DEPTH_LIMIT) return FBS_GOAP_E_INVALID;
  if (req->start->atom_count != (uint32_t)d->atom_count) return FBS_GOAP_E_INVALID;
  if (d->atom_count != p->atom_count) return FBS_GOAP_E_INVALID; /* domain cleared under us */
  if (!fbs_goal_rows_valid(d, req->goal, req->goal_len)) return FBS_GOAP_E_INVALID;
  if (req->cost_override) {
    for (i = 0u; i < d->action_count; ++i)
      if (!fbs_cost_ok(req->cost_override[i])) return FBS_GOAP_E_RANGE;
  }

  cap_nodes = req->max_nodes ? req->max_nodes : p->max_nodes;
  cap_depth = req->max_depth ? req->max_depth : p->max_depth;

  res.outcome = FBS_GOAP_UNSOLVABLE;
  res.plan_len = 0u;
  res.plan_cost = 0;
  res.nodes_expanded = 0u;
  res.nodes_generated = 0u;
  res.peak_open = 0u;

  /* Cheapest achiever costs for H_MAX_UNSAT. The sealed domain's table is
   * computed from base costs; a cost_override may lower one, so recompute
   * against the effective costs to keep the heuristic admissible. */
  if (req->heuristic == FBS_GOAP_H_MAX_UNSAT) {
    if (!req->cost_override) {
      for (i = 0u; i < d->atom_count; ++i) p->cheapest[i] = d->atoms[i].cheapest;
    } else {
      for (i = 0u; i < d->atom_count; ++i) p->cheapest[i] = FBS_GOAP_COST_MAX;
      for (i = 0u; i < d->eff_count; ++i) {
        fbs_goap_cost c = req->cost_override[d->effs[i].action];
        if (c < p->cheapest[d->effs[i].atom]) p->cheapest[d->effs[i].atom] = c;
      }
    }
  }

  if (fbs_rows_hold(d, req->start, req->goal, req->goal_len)) {
    res.outcome = FBS_GOAP_ALREADY_SATISFIED;
    *out = res;
    return FBS_GOAP_OK;
  }

  /* Fresh search state. Nothing survives a call except the buffers. */
  memset(p->index, 0, (size_t)p->index_cap * sizeof(unsigned));
  p->node_count = 0u;
  p->heap_len = 0u;

  root = 0u;
  p->node_count = 1u;
  memcpy(p->states, req->start, p->state_size);
  p->nodes[root].g = 0;
  p->nodes[root].h = fbs_heuristic(p, fbs_node_state(p, root), req->heuristic, req->goal, req->goal_len);
  p->nodes[root].f = p->nodes[root].h;
  p->nodes[root].parent = FBS_GOAP_NODE_NONE;
  p->nodes[root].seq = 0u;
  p->nodes[root].next_same = FBS_GOAP_NODE_NONE;
  p->nodes[root].action = FBS_GOAP_ACTION_NONE;
  p->nodes[root].depth = 0u;
  p->nodes[root].dead = 0u;
  p->heap_pos[root] = FBS_GOAP_NODE_NONE;
  p->index[fbs_index_slot(p, p->states)] = root + 1u;
  fbs_heap_push(p, root);
  res.peak_open = 1u;

  while (p->heap_len > 0u && !stop) {
    unsigned cur = fbs_heap_pop(p);
    fbs_goap_state *cur_state = fbs_node_state(p, cur);
    fbs_goap_cost cur_g = p->nodes[cur].g;
    uint16_t cur_depth = p->nodes[cur].depth;
    unsigned act;

    /* A dominated node is skipped whole: the node that superseded it has the
     * same state at no greater depth and no greater g, so it is both a goal in
     * exactly the same cases and a strictly better parent. */
    if (p->nodes[cur].dead) continue;

    if (fbs_rows_hold(d, cur_state, req->goal, req->goal_len)) {
      found = cur;
      outcome = FBS_GOAP_FOUND;
      break;
    }
    if (res.nodes_expanded >= cap_nodes) {
      outcome = FBS_GOAP_NODE_CAP;
      break;
    }
    if ((unsigned)cur_depth >= cap_depth) {
      /* Popped, deliberately not expanded. Because depth is part of the node
       * identity, the shorter route to this same state is a different node and
       * is still in play, so capping here loses nothing that fits the cap: the
       * search stays complete for plans of length <= max_depth, and no node
       * deeper than the cap is ever created (plan_len <= max_depth always). */
      depth_capped = 1;
      continue;
    }
    res.nodes_expanded += 1u;

    for (act = 0u; act < d->action_count; ++act) { /* ascending action id */
      fbs_goap_cost cost, g2;
      uint16_t depth2 = (uint16_t)(cur_depth + 1u);
      unsigned slot, n, exact = FBS_GOAP_NODE_NONE, touched;
      int dominated = 0;

      if (!fbs_pre_holds(d, cur_state, (fbs_goap_action)act)) continue;
      if (req->proc_pre && !req->proc_pre(req->user, (fbs_goap_action)act, cur_state)) continue;

      cost = req->cost_override ? req->cost_override[act] : d->actions[act].cost;
      if (cur_g > FBS_GOAP_COST_MAX - cost) return FBS_GOAP_E_RANGE; /* outputs untouched */
      g2 = (fbs_goap_cost)(cur_g + cost);

      memcpy(p->succ, cur_state, p->state_size);
      fbs_apply_effects(d, (fbs_goap_state *)(void *)p->succ, (fbs_goap_action)act);

      /* Walk every depth already recorded for this state: a live node that is
       * no deeper and no dearer dominates the candidate outright, and the node
       * at exactly this depth is the only one a relaxation may touch. */
      slot = fbs_index_slot(p, p->succ);
      for (n = fbs_index_head(p, slot); n != FBS_GOAP_NODE_NONE; n = p->nodes[n].next_same) {
        if (p->nodes[n].dead) continue;
        if (p->nodes[n].depth <= depth2 && p->nodes[n].g <= g2) {
          dominated = 1;
          break;
        }
        if (p->nodes[n].depth == depth2) exact = n;
      }
      if (dominated) continue;

      if (exact != FBS_GOAP_NODE_NONE) {
        /* Same (state, depth), strictly lower g — the dominance test above
         * already ruled out an equal or cheaper one. Depth is identity and is
         * not rewritten; re-open if this node had already been expanded. */
        p->nodes[exact].g = g2;
        p->nodes[exact].f = fbs_cost_sat_add(g2, p->nodes[exact].h);
        p->nodes[exact].parent = cur;
        p->nodes[exact].action = (uint16_t)act;
        if (p->heap_pos[exact] == FBS_GOAP_NODE_NONE) {
          fbs_heap_push(p, exact);
          if (p->heap_len > res.peak_open) res.peak_open = p->heap_len;
        } else {
          fbs_heap_sift_up(p, p->heap_pos[exact]);
        }
        touched = exact;
      } else {
        unsigned fresh;
        if (p->node_count >= p->max_nodes) { /* node storage exhausted */
          outcome = FBS_GOAP_NODE_CAP;
          stop = 1;
          break;
        }
        fresh = p->node_count;
        p->node_count += 1u;
        memcpy(p->states + (size_t)fresh * p->state_size, p->succ, p->state_size);
        p->nodes[fresh].g = g2;
        p->nodes[fresh].h =
            fbs_heuristic(p, fbs_node_state(p, fresh), req->heuristic, req->goal, req->goal_len);
        p->nodes[fresh].f = fbs_cost_sat_add(g2, p->nodes[fresh].h);
        p->nodes[fresh].parent = cur;
        p->nodes[fresh].seq = next_seq++;
        p->nodes[fresh].next_same = fbs_index_head(p, slot);
        p->nodes[fresh].action = (uint16_t)act;
        p->nodes[fresh].depth = depth2;
        p->nodes[fresh].dead = 0u;
        p->heap_pos[fresh] = FBS_GOAP_NODE_NONE;
        p->index[slot] = fresh + 1u;
        fbs_heap_push(p, fresh);
        res.nodes_generated += 1u;
        if (p->heap_len > res.peak_open) res.peak_open = p->heap_len;
        touched = fresh;
      }
      fbs_index_prune(p, slot, touched);
    }
  }

  if (outcome == FBS_GOAP_UNSOLVABLE && depth_capped) outcome = FBS_GOAP_DEPTH_CAP;

  if (outcome == FBS_GOAP_FOUND) {
    size_t len = (size_t)p->nodes[found].depth;
    res.plan_cost = p->nodes[found].g;
    if (len > plan_cap) {
      res.outcome = FBS_GOAP_PLAN_TRUNCATED;
      res.plan_len = len; /* required length; out_plan is left untouched */
    } else {
      unsigned walk = found;
      size_t w = len;
      while (walk != root) {
        out_plan[--w] = (fbs_goap_action)p->nodes[walk].action;
        walk = p->nodes[walk].parent;
      }
      res.outcome = FBS_GOAP_FOUND;
      res.plan_len = len;
    }
  } else {
    res.outcome = outcome;
    res.plan_len = 0u;
    res.plan_cost = 0;
  }

  *out = res;
  return FBS_GOAP_OK;
}

/* ------------------------------------------------------------------------- */
/* Plan validation                                                           */
/* ------------------------------------------------------------------------- */

/* The working copy lives in the planner's successor scratch, which is sized by
 * the same sealed domain and is not in use outside fbs_goap_plan: validation
 * allocates nothing at all. */
fbs_goap_status fbs_goap_plan_validate(fbs_goap_planner *p, const fbs_goap_state *state,
                                       const fbs_goap_action *plan, size_t plan_len,
                                       const fbs_goap_cond *goal, size_t goal_len,
                                       fbs_goap_proc_pre_fn proc_pre, void *user,
                                       size_t *out_first_invalid, int *out_goal_met) {
  const fbs_goap_domain *d;
  fbs_goap_state *work;
  fbs_goap_status st;
  size_t i;
  size_t first_invalid;
  int goal_met = 0;

  if (!p || !state || !out_first_invalid || !out_goal_met) return FBS_GOAP_E_INVALID;
  if (!plan && plan_len > 0u) return FBS_GOAP_E_INVALID;
  if (!goal && goal_len > 0u) return FBS_GOAP_E_INVALID;
  d = p->domain;
  st = fbs_state_check(d, state);
  if (st != FBS_GOAP_OK) return st;
  if (d->atom_count != p->atom_count) return FBS_GOAP_E_INVALID; /* domain cleared under us */
  if (!fbs_goal_rows_valid(d, goal, goal_len)) return FBS_GOAP_E_INVALID;
  for (i = 0u; i < plan_len; ++i)
    if (!fbs_action_ok(d, plan[i])) return FBS_GOAP_E_INVALID;

  work = (fbs_goap_state *)(void *)p->succ;
  memcpy(work, state, (size_t)p->state_size);

  first_invalid = plan_len;
  for (i = 0u; i < plan_len; ++i) {
    if (!fbs_pre_holds(d, work, plan[i]) || (proc_pre && !proc_pre(user, plan[i], work))) {
      first_invalid = i;
      break;
    }
    fbs_apply_effects(d, work, plan[i]);
  }
  if (first_invalid == plan_len) goal_met = fbs_rows_hold(d, work, goal, goal_len);

  *out_first_invalid = first_invalid;
  *out_goal_met = goal_met;
  return FBS_GOAP_OK;
}

/* ------------------------------------------------------------------------- */
/* Serialization (domain blob "FBSG" version 1, little-endian)               */
/* ------------------------------------------------------------------------- */

static void fbs_put_u16(unsigned char *p, unsigned v) {
  p[0] = (unsigned char)(v & 0xffu);
  p[1] = (unsigned char)((v >> 8) & 0xffu);
}

static void fbs_put_u32(unsigned char *p, unsigned v) {
  p[0] = (unsigned char)(v & 0xffu);
  p[1] = (unsigned char)((v >> 8) & 0xffu);
  p[2] = (unsigned char)((v >> 16) & 0xffu);
  p[3] = (unsigned char)((v >> 24) & 0xffu);
}

static void fbs_put_i32(unsigned char *p, int32_t v) { fbs_put_u32(p, (unsigned)(uint32_t)v); }

static unsigned fbs_get_u16(const unsigned char *p) {
  return (unsigned)p[0] | ((unsigned)p[1] << 8);
}

static unsigned fbs_get_u32(const unsigned char *p) {
  return (unsigned)p[0] | ((unsigned)p[1] << 8) | ((unsigned)p[2] << 16) | ((unsigned)p[3] << 24);
}

static int32_t fbs_get_i32(const unsigned char *p) { return (int32_t)(uint32_t)fbs_get_u32(p); }

size_t fbs_goap_domain_serialized_size(const fbs_goap_domain *d) {
  if (!d || !d->sealed) return 0u;
  return (size_t)FBS_GOAP_HEADER_BYTES + (size_t)d->atom_count * FBS_GOAP_ATOM_BYTES +
         (size_t)d->action_count * (FBS_GOAP_ACTION_BYTES + FBS_GOAP_ACTION_EFF_BYTES) +
         (size_t)d->cond_count * FBS_GOAP_ROW_BYTES + (size_t)d->eff_count * FBS_GOAP_ROW_BYTES +
         (size_t)d->key_top;
}

fbs_goap_status fbs_goap_domain_serialize(const fbs_goap_domain *d, void *buf, size_t cap,
                                          size_t *out_len) {
  unsigned char *p;
  size_t need, off;
  unsigned i, koff;

  if (!d || !out_len) return FBS_GOAP_E_INVALID;
  if (!buf && cap > 0u) return FBS_GOAP_E_INVALID;
  if (!d->sealed) return FBS_GOAP_E_STATE;
  need = fbs_goap_domain_serialized_size(d);
  if (cap < need) {
    *out_len = need;
    return FBS_GOAP_E_TRUNCATED;
  }

  p = (unsigned char *)buf;
  p[0] = 'F';
  p[1] = 'B';
  p[2] = 'S';
  p[3] = 'G';
  fbs_put_u16(p + 4, FBS_GOAP_SCHEMA_VERSION);
  fbs_put_u16(p + 6, 0u); /* flags */
  fbs_put_u16(p + 8, d->atom_count);
  fbs_put_u16(p + 10, d->action_count);
  fbs_put_u32(p + 12, d->cond_count);
  fbs_put_u32(p + 16, d->eff_count);
  fbs_put_u32(p + 20, d->key_top);
  fbs_put_u32(p + 24, 0u); /* reserved */

  off = FBS_GOAP_HEADER_BYTES;
  koff = 0u; /* keys are emitted in atom-then-action id order */
  for (i = 0u; i < d->atom_count; ++i) {
    unsigned char *r = p + off;
    fbs_put_u32(r, koff);
    fbs_put_u32(r + 4, d->atoms[i].key_len);
    fbs_put_i32(r + 8, d->atoms[i].min_value);
    fbs_put_i32(r + 12, d->atoms[i].max_value);
    fbs_put_i32(r + 16, d->atoms[i].default_value);
    koff += d->atoms[i].key_len;
    off += FBS_GOAP_ATOM_BYTES;
  }
  for (i = 0u; i < d->action_count; ++i) {
    unsigned char *r = p + off;
    fbs_put_u32(r, koff);
    fbs_put_u32(r + 4, d->actions[i].key_len);
    fbs_put_i32(r + 8, d->actions[i].cost);
    fbs_put_u32(r + 12, d->actions[i].cond_off);
    fbs_put_u32(r + 16, d->actions[i].cond_count);
    koff += d->actions[i].key_len;
    off += FBS_GOAP_ACTION_BYTES;
  }
  for (i = 0u; i < d->action_count; ++i) {
    unsigned char *r = p + off;
    fbs_put_u32(r, d->actions[i].eff_off);
    fbs_put_u32(r + 4, d->actions[i].eff_count);
    off += FBS_GOAP_ACTION_EFF_BYTES;
  }
  for (i = 0u; i < d->cond_count; ++i) {
    unsigned char *r = p + off;
    fbs_put_u16(r, d->conds[i].atom);
    r[2] = d->conds[i].kind;
    r[3] = 0u;
    fbs_put_i32(r + 4, d->conds[i].value);
    off += FBS_GOAP_ROW_BYTES;
  }
  for (i = 0u; i < d->eff_count; ++i) {
    unsigned char *r = p + off;
    fbs_put_u16(r, d->effs[i].atom);
    r[2] = d->effs[i].kind;
    r[3] = 0u;
    fbs_put_i32(r + 4, d->effs[i].value);
    off += FBS_GOAP_ROW_BYTES;
  }
  for (i = 0u; i < d->atom_count; ++i) {
    memcpy(p + off, d->keys + d->atoms[i].key_off, (size_t)d->atoms[i].key_len);
    off += d->atoms[i].key_len;
  }
  for (i = 0u; i < d->action_count; ++i) {
    memcpy(p + off, d->keys + d->actions[i].key_off, (size_t)d->actions[i].key_len);
    off += d->actions[i].key_len;
  }

  *out_len = need;
  return FBS_GOAP_OK;
}

fbs_goap_status fbs_goap_domain_deserialize(const void *buf, size_t len, const fbs_goap_config *cfg,
                                            const fbs_goap_allocator *alloc, fbs_goap_domain **out) {
  const unsigned char *p = (const unsigned char *)buf;
  const unsigned char *arec, *crec, *erec, *cond, *eff, *keys;
  unsigned atoms, actions, conds, effs, kbytes;
  unsigned i, koff, prev_off;
  size_t need;
  fbs_goap_config c;
  fbs_goap_domain *d = NULL;
  fbs_goap_status st;

  if (!buf || !out) return FBS_GOAP_E_INVALID;
  if (cfg && !fbs_config_valid(cfg)) return FBS_GOAP_E_INVALID;

  if (len < (size_t)FBS_GOAP_HEADER_BYTES) return FBS_GOAP_E_SCHEMA;
  if (p[0] != 'F' || p[1] != 'B' || p[2] != 'S' || p[3] != 'G') return FBS_GOAP_E_SCHEMA;
  if (fbs_get_u16(p + 4) != FBS_GOAP_SCHEMA_VERSION) return FBS_GOAP_E_SCHEMA;
  if (fbs_get_u16(p + 6) != 0u) return FBS_GOAP_E_SCHEMA;
  atoms = fbs_get_u16(p + 8);
  actions = fbs_get_u16(p + 10);
  conds = fbs_get_u32(p + 12);
  effs = fbs_get_u32(p + 16);
  kbytes = fbs_get_u32(p + 20);
  if (fbs_get_u32(p + 24) != 0u) return FBS_GOAP_E_SCHEMA;
  if (atoms > FBS_GOAP_MAX_ATOMS_LIMIT || actions > FBS_GOAP_MAX_ACTIONS_LIMIT) return FBS_GOAP_E_SCHEMA;
  if (conds > FBS_GOAP_MAX_ROWS_LIMIT || effs > FBS_GOAP_MAX_ROWS_LIMIT) return FBS_GOAP_E_SCHEMA;
  if (kbytes > FBS_GOAP_MAX_KEY_BYTES_LIMIT) return FBS_GOAP_E_SCHEMA;

  need = (size_t)FBS_GOAP_HEADER_BYTES + (size_t)atoms * FBS_GOAP_ATOM_BYTES +
         (size_t)actions * (FBS_GOAP_ACTION_BYTES + FBS_GOAP_ACTION_EFF_BYTES) +
         (size_t)conds * FBS_GOAP_ROW_BYTES + (size_t)effs * FBS_GOAP_ROW_BYTES + (size_t)kbytes;
  if (len != need) return FBS_GOAP_E_SCHEMA;

  arec = p + FBS_GOAP_HEADER_BYTES;
  crec = arec + (size_t)atoms * FBS_GOAP_ATOM_BYTES;
  erec = crec + (size_t)actions * FBS_GOAP_ACTION_BYTES;
  cond = erec + (size_t)actions * FBS_GOAP_ACTION_EFF_BYTES;
  eff = cond + (size_t)conds * FBS_GOAP_ROW_BYTES;
  keys = eff + (size_t)effs * FBS_GOAP_ROW_BYTES;

  /* Atoms: canonical key layout, min <= default <= max. */
  koff = 0u;
  for (i = 0u; i < atoms; ++i) {
    const unsigned char *r = arec + (size_t)i * FBS_GOAP_ATOM_BYTES;
    unsigned ko = fbs_get_u32(r), kl = fbs_get_u32(r + 4);
    int32_t lo = fbs_get_i32(r + 8), hi = fbs_get_i32(r + 12), def = fbs_get_i32(r + 16);
    if (kl == 0u || kl > FBS_GOAP_MAX_KEY_LEN) return FBS_GOAP_E_SCHEMA;
    if (ko != koff || kl > kbytes - koff) return FBS_GOAP_E_SCHEMA;
    if (lo > hi || def < lo || def > hi) return FBS_GOAP_E_SCHEMA;
    koff += kl;
  }
  /* Actions: canonical key layout, cost in range, contiguous row slices. */
  prev_off = 0u;
  for (i = 0u; i < actions; ++i) {
    const unsigned char *r = crec + (size_t)i * FBS_GOAP_ACTION_BYTES;
    unsigned ko = fbs_get_u32(r), kl = fbs_get_u32(r + 4);
    int32_t cost = fbs_get_i32(r + 8);
    unsigned co = fbs_get_u32(r + 12), cn = fbs_get_u32(r + 16);
    if (kl == 0u || kl > FBS_GOAP_MAX_KEY_LEN) return FBS_GOAP_E_SCHEMA;
    if (ko != koff || kl > kbytes - koff) return FBS_GOAP_E_SCHEMA;
    if (!fbs_cost_ok(cost)) return FBS_GOAP_E_SCHEMA;
    if (co != prev_off || cn > conds - co) return FBS_GOAP_E_SCHEMA;
    prev_off = co + cn;
    koff += kl;
  }
  if (koff != kbytes) return FBS_GOAP_E_SCHEMA;
  if (prev_off != conds) return FBS_GOAP_E_SCHEMA;
  prev_off = 0u;
  for (i = 0u; i < actions; ++i) {
    const unsigned char *r = erec + (size_t)i * FBS_GOAP_ACTION_EFF_BYTES;
    unsigned eo = fbs_get_u32(r), en = fbs_get_u32(r + 4);
    if (eo != prev_off || en > effs - eo) return FBS_GOAP_E_SCHEMA;
    prev_off = eo + en;
  }
  if (prev_off != effs) return FBS_GOAP_E_SCHEMA;

  /* Rows: valid atom ids and enums, zero padding, canonical order inside each
   * action's slice (strictly ascending, so duplicates cannot survive). */
  for (i = 0u; i < actions; ++i) {
    const unsigned char *r = crec + (size_t)i * FBS_GOAP_ACTION_BYTES;
    unsigned co = fbs_get_u32(r + 12), cn = fbs_get_u32(r + 16), j;
    for (j = 0u; j < cn; ++j) {
      const unsigned char *rw = cond + (size_t)(co + j) * FBS_GOAP_ROW_BYTES;
      unsigned a = fbs_get_u16(rw);
      unsigned k = (unsigned)rw[2];
      int32_t v = fbs_get_i32(rw + 4);
      if (rw[3] != 0u) return FBS_GOAP_E_SCHEMA;
      if (a >= atoms || !fbs_is_cmp((int)k)) return FBS_GOAP_E_SCHEMA;
      if (j > 0u) {
        const unsigned char *pv = cond + (size_t)(co + j - 1u) * FBS_GOAP_ROW_BYTES;
        unsigned pa = fbs_get_u16(pv), pk = (unsigned)pv[2];
        int32_t vv = fbs_get_i32(pv + 4);
        if (!(pa < a || (pa == a && (pk < k || (pk == k && vv < v))))) return FBS_GOAP_E_SCHEMA;
      }
    }
  }
  for (i = 0u; i < actions; ++i) {
    const unsigned char *r = erec + (size_t)i * FBS_GOAP_ACTION_EFF_BYTES;
    unsigned eo = fbs_get_u32(r), en = fbs_get_u32(r + 4), j;
    for (j = 0u; j < en; ++j) {
      const unsigned char *rw = eff + (size_t)(eo + j) * FBS_GOAP_ROW_BYTES;
      unsigned a = fbs_get_u16(rw);
      unsigned k = (unsigned)rw[2];
      int32_t v = fbs_get_i32(rw + 4);
      if (rw[3] != 0u) return FBS_GOAP_E_SCHEMA;
      if (a >= atoms || !fbs_is_op((int)k)) return FBS_GOAP_E_SCHEMA;
      if (k == (unsigned)FBS_GOAP_SET) {
        const unsigned char *ar = arec + (size_t)a * FBS_GOAP_ATOM_BYTES;
        if (v < fbs_get_i32(ar + 8) || v > fbs_get_i32(ar + 12)) return FBS_GOAP_E_SCHEMA;
      }
      if (j > 0u) {
        const unsigned char *pv = eff + (size_t)(eo + j - 1u) * FBS_GOAP_ROW_BYTES;
        unsigned pa = fbs_get_u16(pv);
        /* at most one effect per (action, atom), so atoms strictly ascend */
        if (pa >= a) return FBS_GOAP_E_SCHEMA;
      }
    }
  }

  if (cfg) {
    c = *cfg;
    if (c.max_atoms < atoms || c.max_actions < actions || c.max_conditions < conds ||
        c.max_effects < effs || c.max_key_bytes < kbytes)
      return FBS_GOAP_E_FULL;
  } else {
    c = fbs_goap_config_default();
    if (c.max_atoms < atoms) c.max_atoms = atoms;
    if (c.max_actions < actions) c.max_actions = actions;
    if (c.max_conditions < conds) c.max_conditions = conds;
    if (c.max_effects < effs) c.max_effects = effs;
    if (c.max_key_bytes < kbytes) c.max_key_bytes = kbytes;
  }

  st = fbs_domain_alloc(&c, alloc, &d);
  if (st != FBS_GOAP_OK) return st;

  for (i = 0u; i < atoms; ++i) {
    const unsigned char *r = arec + (size_t)i * FBS_GOAP_ATOM_BYTES;
    unsigned ko = fbs_get_u32(r), kl = fbs_get_u32(r + 4);
    fbs_goap_atom_rec *rec = &d->atoms[i];
    if (fbs_atom_lookup(d, (const char *)keys + ko, (size_t)kl) != 0xFFFFFFFFu) {
      fbs_goap_domain_destroy(d);
      return FBS_GOAP_E_SCHEMA; /* duplicate atom key */
    }
    rec->key_off = d->key_top;
    rec->key_len = kl;
    rec->min_value = fbs_get_i32(r + 8);
    rec->max_value = fbs_get_i32(r + 12);
    rec->default_value = fbs_get_i32(r + 16);
    rec->cheapest = FBS_GOAP_COST_MAX;
    memcpy(d->keys + d->key_top, keys + ko, (size_t)kl);
    d->key_top += kl;
    d->atom_count = i + 1u;
    fbs_key_insert(d->atom_hash, d->atom_hash_cap, d->keys, (const char *)keys + ko, (size_t)kl, i);
  }
  for (i = 0u; i < actions; ++i) {
    const unsigned char *r = crec + (size_t)i * FBS_GOAP_ACTION_BYTES;
    const unsigned char *er = erec + (size_t)i * FBS_GOAP_ACTION_EFF_BYTES;
    unsigned ko = fbs_get_u32(r), kl = fbs_get_u32(r + 4);
    fbs_goap_action_rec *rec = &d->actions[i];
    if (fbs_action_lookup(d, (const char *)keys + ko, (size_t)kl) != 0xFFFFFFFFu) {
      fbs_goap_domain_destroy(d);
      return FBS_GOAP_E_SCHEMA; /* duplicate action key */
    }
    rec->key_off = d->key_top;
    rec->key_len = kl;
    rec->cost = fbs_get_i32(r + 8);
    rec->cond_off = fbs_get_u32(r + 12);
    rec->cond_count = fbs_get_u32(r + 16);
    rec->eff_off = fbs_get_u32(er);
    rec->eff_count = fbs_get_u32(er + 4);
    memcpy(d->keys + d->key_top, keys + ko, (size_t)kl);
    d->key_top += kl;
    d->action_count = i + 1u;
    fbs_key_insert(d->action_hash, d->action_hash_cap, d->keys, (const char *)keys + ko, (size_t)kl, i);
  }
  for (i = 0u; i < conds; ++i) {
    const unsigned char *rw = cond + (size_t)i * FBS_GOAP_ROW_BYTES;
    d->conds[i].atom = (uint16_t)fbs_get_u16(rw);
    d->conds[i].kind = rw[2];
    d->conds[i].pad = 0u;
    d->conds[i].value = fbs_get_i32(rw + 4);
    d->conds[i].action = 0u;
  }
  for (i = 0u; i < effs; ++i) {
    const unsigned char *rw = eff + (size_t)i * FBS_GOAP_ROW_BYTES;
    d->effs[i].atom = (uint16_t)fbs_get_u16(rw);
    d->effs[i].kind = rw[2];
    d->effs[i].pad = 0u;
    d->effs[i].value = fbs_get_i32(rw + 4);
    d->effs[i].action = 0u;
  }
  /* Rows carry their owning action so the arrays stay sortable and listable. */
  for (i = 0u; i < actions; ++i) {
    unsigned j;
    for (j = 0u; j < d->actions[i].cond_count; ++j)
      d->conds[d->actions[i].cond_off + j].action = (uint16_t)i;
    for (j = 0u; j < d->actions[i].eff_count; ++j)
      d->effs[d->actions[i].eff_off + j].action = (uint16_t)i;
  }
  d->cond_count = conds;
  d->eff_count = effs;

  /* The blob is already canonically ordered; seal only recomputes the derived
   * table and flips the flag. */
  st = fbs_goap_domain_seal(d);
  if (st != FBS_GOAP_OK) {
    fbs_goap_domain_destroy(d);
    return st;
  }

  *out = d;
  return FBS_GOAP_OK;
}
