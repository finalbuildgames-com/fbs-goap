/*
 * fbs/goap.h — FinalBuildSystems goal-oriented action planner. C99, engine
 * independent, no libm.
 *
 * Model: a DOMAIN registers atoms (named int32 slots with a declared
 * [min, max] range) and actions (precondition rows with comparators,
 * effect rows SET/ADD with clamping, an integer base cost), then is sealed.
 * A STATE is a caller-owned blob of slot
 * values plus a "known" bitmap. A PLANNER owns the search memory for a sealed
 * domain (one allocation) and is reusable; planning is a pure function of
 * (domain, planner capacity, request): forward best-first search over states
 * with integer costs, an explicit outcome, a hard node cap and a total
 * deterministic tie order (f ascending, g descending, insertion sequence
 * ascending). No globals; a const domain may be planned against by several
 * planners concurrently. Errors leave outputs untouched except
 * FBS_GOAP_E_TRUNCATED (required size reported).
 */
#ifndef FBS_GOAP_H
#define FBS_GOAP_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define FBS_GOAP_VERSION 100

typedef uint16_t fbs_goap_atom;
typedef uint16_t fbs_goap_action;
#define FBS_GOAP_ATOM_NONE ((fbs_goap_atom)0xFFFFu)
#define FBS_GOAP_ACTION_NONE ((fbs_goap_action)0xFFFFu)

typedef int32_t fbs_goap_cost;
#define FBS_GOAP_COST_MAX ((fbs_goap_cost)0x3FFFFFFF)

typedef enum fbs_goap_status {
  FBS_GOAP_OK = 0,
  FBS_GOAP_E_INVALID = -1,   /* NULL pointer, bad enum, unknown atom/action id, empty key, request outside planner capacity */
  FBS_GOAP_E_NOT_FOUND = -2, /* no atom/action with that key; state slot unknown */
  FBS_GOAP_E_EXISTS = -3,    /* key already registered; *out untouched */
  FBS_GOAP_E_FULL = -4,      /* a config capacity is exhausted */
  FBS_GOAP_E_RANGE = -5,     /* cost outside [0, FBS_GOAP_COST_MAX], value outside the atom's [min, max], min > max, cost sum overflow */
  FBS_GOAP_E_SCHEMA = -6,    /* blob magic/version/length/consistency mismatch */
  FBS_GOAP_E_TRUNCATED = -7, /* output too small; required count/length written */
  FBS_GOAP_E_SEALED = -8,    /* registration attempted on a sealed domain */
  FBS_GOAP_E_STATE = -9,     /* operation needs a sealed domain (planning, states, serialization) */
  FBS_GOAP_E_MEMORY = -10    /* allocator returned NULL */
} fbs_goap_status;

const char *fbs_goap_status_name(int status);
unsigned fbs_goap_version(void);

typedef struct fbs_goap_allocator {
  void *(*alloc)(void *user, size_t bytes);
  void (*free)(void *user, void *ptr);
  void *user;
} fbs_goap_allocator;

/* ------------------------------------------------------------------------- */
/* Domain                                                                    */
/* ------------------------------------------------------------------------- */

typedef struct fbs_goap_config {
  unsigned max_atoms;      /* 1..4096 */
  unsigned max_actions;    /* 1..4096 */
  unsigned max_conditions; /* total precondition rows across all actions, >= 0, <= 1<<20 */
  unsigned max_effects;    /* total effect rows across all actions, >= 0, <= 1<<20 */
  unsigned max_key_bytes;  /* total key storage for atom + action names, 1..1<<26 */
} fbs_goap_config;

/* 64 atoms, 64 actions, 512 conditions, 512 effects, 4096 key bytes. */
fbs_goap_config fbs_goap_config_default(void);

typedef struct fbs_goap_domain fbs_goap_domain;

fbs_goap_status fbs_goap_domain_create(const fbs_goap_config *cfg, const fbs_goap_allocator *alloc,
                                       fbs_goap_domain **out);
void fbs_goap_domain_destroy(fbs_goap_domain *d);
/* Removes every atom and action and unseals. */
void fbs_goap_domain_clear(fbs_goap_domain *d);
size_t fbs_goap_domain_memory(const fbs_goap_domain *d);

/* Keys are byte strings (UTF-8 by convention), compared bytewise, 1..255 bytes,
 * copied. Atom and action keys are separate namespaces. */
fbs_goap_status fbs_goap_atom_add(fbs_goap_domain *d, const char *key, size_t key_len,
                                  int32_t min_value, int32_t max_value, int32_t default_value,
                                  fbs_goap_atom *out);
fbs_goap_status fbs_goap_atom_find(const fbs_goap_domain *d, const char *key, size_t key_len,
                                   fbs_goap_atom *out);
unsigned fbs_goap_atom_count(const fbs_goap_domain *d);
fbs_goap_status fbs_goap_atom_key(const fbs_goap_domain *d, fbs_goap_atom a, const char **out_key,
                                  size_t *out_len);
fbs_goap_status fbs_goap_atom_range(const fbs_goap_domain *d, fbs_goap_atom a, int32_t *out_min,
                                    int32_t *out_max, int32_t *out_default);

typedef enum fbs_goap_cmp {
  FBS_GOAP_EQ = 0, FBS_GOAP_NE = 1, FBS_GOAP_LT = 2, FBS_GOAP_LE = 3, FBS_GOAP_GT = 4, FBS_GOAP_GE = 5
} fbs_goap_cmp;

typedef enum fbs_goap_effect_op {
  FBS_GOAP_SET = 0, /* slot = value (value must lie in [min, max]) */
  FBS_GOAP_ADD = 1  /* slot += value, then clamped to [min, max]; value may be negative */
} fbs_goap_effect_op;

typedef struct fbs_goap_cond {
  fbs_goap_atom atom;
  uint8_t cmp; /* fbs_goap_cmp */
  uint8_t pad;
  int32_t value;
} fbs_goap_cond;

typedef struct fbs_goap_effect {
  fbs_goap_atom atom;
  uint8_t op; /* fbs_goap_effect_op */
  uint8_t pad;
  int32_t value;
} fbs_goap_effect;

fbs_goap_status fbs_goap_action_add(fbs_goap_domain *d, const char *key, size_t key_len,
                                    fbs_goap_cost base_cost, fbs_goap_action *out);
fbs_goap_status fbs_goap_action_find(const fbs_goap_domain *d, const char *key, size_t key_len,
                                     fbs_goap_action *out);
unsigned fbs_goap_action_count(const fbs_goap_domain *d);
fbs_goap_status fbs_goap_action_key(const fbs_goap_domain *d, fbs_goap_action act,
                                    const char **out_key, size_t *out_len);
fbs_goap_status fbs_goap_action_cost(const fbs_goap_domain *d, fbs_goap_action act, fbs_goap_cost *out);
/* A precondition on an unknown slot is unsatisfied. Duplicate identical rows are rejected (E_EXISTS). */
fbs_goap_status fbs_goap_action_pre(fbs_goap_domain *d, fbs_goap_action act, fbs_goap_atom a, int cmp,
                                    int32_t value);
/* At most one effect per (action, atom): a second one is E_EXISTS. */
fbs_goap_status fbs_goap_action_effect(fbs_goap_domain *d, fbs_goap_action act, fbs_goap_atom a, int op,
                                       int32_t value);
/* Sorted by (atom, cmp, value) / (atom, op, value) after seal; before seal in registration order. */
fbs_goap_status fbs_goap_action_conditions(const fbs_goap_domain *d, fbs_goap_action act,
                                           fbs_goap_cond *out, size_t cap, size_t *count);
fbs_goap_status fbs_goap_action_effects(const fbs_goap_domain *d, fbs_goap_action act,
                                        fbs_goap_effect *out, size_t cap, size_t *count);

/* Freezes registration, sorts rows canonically and precomputes the per-atom
 * cheapest achiever costs used by FBS_GOAP_H_MAX_UNSAT. Idempotent. */
fbs_goap_status fbs_goap_domain_seal(fbs_goap_domain *d);
int fbs_goap_domain_is_sealed(const fbs_goap_domain *d);

/* ------------------------------------------------------------------------- */
/* State (caller-owned blob: atom_count, known bitmap, one i32 per atom)     */
/* ------------------------------------------------------------------------- */

typedef struct fbs_goap_state fbs_goap_state;

/* Bytes per state for a sealed domain; 0 for NULL or an unsealed domain. */
size_t fbs_goap_state_size(const fbs_goap_domain *d);
/* buf must hold fbs_goap_state_size bytes, 4-byte aligned; every slot starts unknown (value 0). */
fbs_goap_status fbs_goap_state_init(const fbs_goap_domain *d, void *buf, size_t cap, fbs_goap_state **out);
/* Every slot known at its atom default. */
fbs_goap_status fbs_goap_state_init_defaults(const fbs_goap_domain *d, void *buf, size_t cap,
                                             fbs_goap_state **out);
fbs_goap_status fbs_goap_state_copy(const fbs_goap_domain *d, fbs_goap_state *dst, const fbs_goap_state *src);
fbs_goap_status fbs_goap_state_set(const fbs_goap_domain *d, fbs_goap_state *s, fbs_goap_atom a, int32_t value);
fbs_goap_status fbs_goap_state_unset(const fbs_goap_domain *d, fbs_goap_state *s, fbs_goap_atom a);
int fbs_goap_state_known(const fbs_goap_domain *d, const fbs_goap_state *s, fbs_goap_atom a);
fbs_goap_status fbs_goap_state_get(const fbs_goap_domain *d, const fbs_goap_state *s, fbs_goap_atom a,
                                   int32_t *out);
/* Byte-exact comparison (unknown slots are canonical zeros). 1, 0, or negative on error. */
int fbs_goap_state_equal(const fbs_goap_domain *d, const fbs_goap_state *a, const fbs_goap_state *b);
/* 1 when every goal row holds (unknown slots never satisfy), 0 otherwise, negative on error. */
int fbs_goap_state_satisfies(const fbs_goap_domain *d, const fbs_goap_state *s, const fbs_goap_cond *goal,
                             size_t goal_len);
/* Applies one action's effects (no precondition check): the executor's model update. */
fbs_goap_status fbs_goap_apply(const fbs_goap_domain *d, fbs_goap_state *s, fbs_goap_action act);
/* 1 when the action's symbolic preconditions hold in s. */
int fbs_goap_action_applicable(const fbs_goap_domain *d, const fbs_goap_state *s, fbs_goap_action act);

/* ------------------------------------------------------------------------- */
/* Planner                                                                   */
/* ------------------------------------------------------------------------- */

typedef struct fbs_goap_planner fbs_goap_planner;

typedef struct fbs_goap_planner_config {
  unsigned max_nodes;  /* search node capacity and default node cap, 1..1<<22 */
  unsigned max_depth;  /* default plan-length cap, 1..65535 */
} fbs_goap_planner_config;

/* 4096 nodes, depth 64. */
fbs_goap_planner_config fbs_goap_planner_config_default(void);

/* One allocation sized by the sealed domain and the config; the domain must
 * outlive the planner and must not be cleared while planners reference it. */
fbs_goap_status fbs_goap_planner_create(const fbs_goap_domain *d, const fbs_goap_planner_config *cfg,
                                        const fbs_goap_allocator *alloc, fbs_goap_planner **out);
void fbs_goap_planner_destroy(fbs_goap_planner *p);
size_t fbs_goap_planner_memory(const fbs_goap_planner *p);

typedef enum fbs_goap_heuristic {
  FBS_GOAP_H_ZERO = 0,     /* uniform-cost search: optimal by construction (default) */
  FBS_GOAP_H_MAX_UNSAT = 1 /* max over unsatisfied goal rows of the cheapest achiever cost: admissible */
} fbs_goap_heuristic;

typedef enum fbs_goap_outcome {
  FBS_GOAP_FOUND = 0,             /* an optimal plan was written */
  FBS_GOAP_ALREADY_SATISFIED = 1, /* the start state satisfies the goal; plan_len 0, cost 0, no expansion */
  FBS_GOAP_UNSOLVABLE = 2,        /* reachable space exhausted within the caps: proven */
  FBS_GOAP_NODE_CAP = 3,          /* node cap reached without a proof either way */
  FBS_GOAP_DEPTH_CAP = 4,         /* no goal found; at least one live frontier node hit the depth cap */
  FBS_GOAP_PLAN_TRUNCATED = 5     /* plan found but plan_cap is too small; plan_len = required length */
} fbs_goap_outcome;

/* Must be a pure function of (user, act, state): the planner may call it any
 * number of times per state and relies on identical answers. 0 = not
 * applicable, non-zero = applicable. NULL means every action is applicable. */
typedef int (*fbs_goap_proc_pre_fn)(void *user, fbs_goap_action act, const fbs_goap_state *s);

typedef struct fbs_goap_request {
  const fbs_goap_state *start;   /* must be a state of the planner's domain */
  const fbs_goap_cond *goal;     /* partial specification; goal_len >= 1 */
  size_t goal_len;
  int heuristic;                 /* fbs_goap_heuristic */
  unsigned max_nodes;            /* 0 = planner capacity; larger than capacity is E_INVALID */
  unsigned max_depth;            /* 0 = planner default */
  const fbs_goap_cost *cost_override; /* NULL, or fbs_goap_action_count(d) per-agent costs in [0, COST_MAX] */
  fbs_goap_proc_pre_fn proc_pre; /* optional */
  void *user;
} fbs_goap_request;

typedef struct fbs_goap_result {
  int outcome;              /* fbs_goap_outcome */
  size_t plan_len;          /* steps written, or the required length when PLAN_TRUNCATED */
  fbs_goap_cost plan_cost;  /* total cost of the found plan (also for PLAN_TRUNCATED); 0 when no plan */
  unsigned nodes_expanded;  /* always reported */
  unsigned nodes_generated;
  unsigned peak_open;
} fbs_goap_result;

/* Plan steps are written in execution order (out_plan[0] first). Returns
 * FBS_GOAP_OK whenever the search reached a defined conclusion; read
 * out->outcome. Negative statuses (bad request, unsealed domain, cost
 * overflow) leave out_plan and *out untouched. Tie order is total:
 * (f ascending, g descending, insertion sequence ascending); successors are
 * generated in ascending action id. Search nodes are identified by
 * (state, depth): a state re-enters the open set at a given depth only with
 * a strictly lower g, and distinct depths are distinct nodes, so the depth
 * cap is sound and complete (FOUND is optimal among plans of length
 * <= max_depth; DEPTH_CAP only when no plan of that length exists within the
 * node cap). */
fbs_goap_status fbs_goap_plan(fbs_goap_planner *p, const fbs_goap_request *req, fbs_goap_action *out_plan,
                              size_t plan_cap, fbs_goap_result *out);

/* Walks `plan` from `state` applying effects, checking each step's symbolic
 * preconditions and proc_pre; *out_first_invalid = index of the first step
 * that cannot execute, or plan_len when the whole plan holds; when the whole
 * plan holds, *out_goal_met reports whether the final state satisfies the goal.
 * Uses the planner's scratch memory (no allocation); the planner's domain is
 * the plan's domain. */
fbs_goap_status fbs_goap_plan_validate(fbs_goap_planner *p, const fbs_goap_state *state,
                                       const fbs_goap_action *plan, size_t plan_len,
                                       const fbs_goap_cond *goal, size_t goal_len,
                                       fbs_goap_proc_pre_fn proc_pre, void *user,
                                       size_t *out_first_invalid, int *out_goal_met);

/* ------------------------------------------------------------------------- */
/* Serialization (sealed domains only; little-endian "FBSG" version 1)       */
/* ------------------------------------------------------------------------- */

size_t fbs_goap_domain_serialized_size(const fbs_goap_domain *d); /* 0 for NULL or unsealed */
fbs_goap_status fbs_goap_domain_serialize(const fbs_goap_domain *d, void *buf, size_t cap, size_t *out_len);
/* cfg NULL: capacities are the larger of the defaults and what the blob needs. The result is sealed. */
fbs_goap_status fbs_goap_domain_deserialize(const void *buf, size_t len, const fbs_goap_config *cfg,
                                            const fbs_goap_allocator *alloc, fbs_goap_domain **out);

#ifdef __cplusplus
}
#endif
#endif /* FBS_GOAP_H */
