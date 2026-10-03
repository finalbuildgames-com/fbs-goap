/*
 * tests/test_goap.c — witnesses for include/fbs/goap.h.
 *
 * Self-contained: no test framework. Exit code = number of failures (clamped
 * to 100 so it survives the 8-bit exit status; the true count is printed).
 *
 * Covers witnesses T-1 .. T-13, T-15 and T-16 (T-14, a combined demo with
 * other modules, is not part of this suite), plus
 * NULL/bad-enum validation on every entry point, allocator failure, every
 * capacity exhaustion, every E_TRUNCATED path, the status-name/version
 * functions and two committed golden fixtures.
 *
 *   ./fbs_test_goap                     compare against tests/fixtures/goap/
 *   ./fbs_test_goap --write-fixtures    rewrite those files
 *   ./fbs_test_goap --fixture-dir DIR   look for fixtures under DIR
 */

#include "fbs/goap.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ------------------------------------------------------------------------- */
/* Harness                                                                   */
/* ------------------------------------------------------------------------- */

static int g_checks = 0;
static int g_fails = 0;

static void check_impl(int cond, const char *expr, const char *file, int line) {
  ++g_checks;
  if (!cond) {
    ++g_fails;
    printf("FAIL %s:%d: %s\n", file, line, expr);
  }
}

#define CHECK(expr) check_impl((expr) ? 1 : 0, #expr, __FILE__, __LINE__)

static const char *g_fixture_dir = "fixtures/goap";
static int g_write_fixtures = 0;

static int untouched(const void *p, size_t n, unsigned char fill) {
  const unsigned char *b = (const unsigned char *)p;
  size_t i;
  for (i = 0; i < n; ++i)
    if (b[i] != fill) return 0;
  return 1;
}

/* Deterministic 32-bit xorshift; no rand() anywhere (T-8 requires a fixed,
 * documented seed). */
static uint32_t g_rng = 0x9e3779b9u;

static void rng_seed(uint32_t seed) { g_rng = seed ? seed : 1u; }

static uint32_t rng_next(void) {
  uint32_t x = g_rng;
  x = (uint32_t)(x ^ (x << 13));
  x = (uint32_t)(x ^ (x >> 17));
  x = (uint32_t)(x ^ (x << 5));
  g_rng = x;
  return x;
}

static unsigned rng_below(unsigned n) { return n ? (unsigned)(rng_next() % n) : 0u; }

/* Counting allocator. */
typedef struct {
  int allocs;
  int frees;
  size_t bytes;
  int budget; /* < 0: unlimited, else the number of allocations still allowed */
} counting_alloc;

static void *ca_alloc(void *user, size_t bytes) {
  counting_alloc *c = (counting_alloc *)user;
  if (c->budget == 0) return NULL;
  if (c->budget > 0) --c->budget;
  ++c->allocs;
  c->bytes += bytes;
  return malloc(bytes);
}

static void ca_free(void *user, void *ptr) {
  counting_alloc *c = (counting_alloc *)user;
  if (!ptr) return;
  ++c->frees;
  free(ptr);
}

/* ------------------------------------------------------------------------- */
/* Small helpers                                                             */
/* ------------------------------------------------------------------------- */

/* 1024 bytes of 4-byte-aligned state storage: enough for 250 atoms. */
#define STATE_WORDS 256
typedef struct {
  uint32_t w[STATE_WORDS];
} state_buf;

static fbs_goap_domain *make_domain(void) {
  fbs_goap_domain *d = NULL;
  CHECK(fbs_goap_domain_create(NULL, NULL, &d) == FBS_GOAP_OK);
  return d;
}

static fbs_goap_atom atom_add(fbs_goap_domain *d, const char *key, int32_t lo, int32_t hi,
                              int32_t def) {
  fbs_goap_atom a = FBS_GOAP_ATOM_NONE;
  CHECK(fbs_goap_atom_add(d, key, strlen(key), lo, hi, def, &a) == FBS_GOAP_OK);
  return a;
}

static fbs_goap_action action_add(fbs_goap_domain *d, const char *key, fbs_goap_cost cost) {
  fbs_goap_action act = FBS_GOAP_ACTION_NONE;
  CHECK(fbs_goap_action_add(d, key, strlen(key), cost, &act) == FBS_GOAP_OK);
  return act;
}

static fbs_goap_cond mk_cond(fbs_goap_atom a, int cmp, int32_t v) {
  fbs_goap_cond c;
  c.atom = a;
  c.cmp = (uint8_t)cmp;
  c.pad = 0u;
  c.value = v;
  return c;
}

static fbs_goap_effect mk_effect(fbs_goap_atom a, int op, int32_t v) {
  fbs_goap_effect e;
  e.atom = a;
  e.op = (uint8_t)op;
  e.pad = 0u;
  e.value = v;
  return e;
}

/* Adds rows forward or in reverse registration order (T-6b). */
static void add_pres(fbs_goap_domain *d, fbs_goap_action act, const fbs_goap_cond *rows, size_t n,
                     int reverse) {
  size_t i;
  for (i = 0; i < n; ++i) {
    const fbs_goap_cond *r = reverse ? &rows[n - 1u - i] : &rows[i];
    CHECK(fbs_goap_action_pre(d, act, r->atom, (int)r->cmp, r->value) == FBS_GOAP_OK);
  }
}

static void add_effs(fbs_goap_domain *d, fbs_goap_action act, const fbs_goap_effect *rows, size_t n,
                     int reverse) {
  size_t i;
  for (i = 0; i < n; ++i) {
    const fbs_goap_effect *r = reverse ? &rows[n - 1u - i] : &rows[i];
    CHECK(fbs_goap_action_effect(d, act, r->atom, (int)r->op, r->value) == FBS_GOAP_OK);
  }
}

static fbs_goap_state *state_new(const fbs_goap_domain *d, state_buf *b) {
  fbs_goap_state *s = NULL;
  CHECK(fbs_goap_state_size(d) <= sizeof b->w);
  CHECK(fbs_goap_state_init(d, b->w, sizeof b->w, &s) == FBS_GOAP_OK);
  return s;
}

static fbs_goap_state *state_new_defaults(const fbs_goap_domain *d, state_buf *b) {
  fbs_goap_state *s = NULL;
  CHECK(fbs_goap_state_size(d) <= sizeof b->w);
  CHECK(fbs_goap_state_init_defaults(d, b->w, sizeof b->w, &s) == FBS_GOAP_OK);
  return s;
}

static void state_put(const fbs_goap_domain *d, fbs_goap_state *s, fbs_goap_atom a, int32_t v) {
  CHECK(fbs_goap_state_set(d, s, a, v) == FBS_GOAP_OK);
}

/* "scout approach detonatebomb" */
static void plan_to_keys(const fbs_goap_domain *d, const fbs_goap_action *plan, size_t n, char *out,
                         size_t cap) {
  size_t i, w = 0;
  out[0] = '\0';
  for (i = 0; i < n; ++i) {
    const char *key = NULL;
    size_t len = 0;
    CHECK(fbs_goap_action_key(d, plan[i], &key, &len) == FBS_GOAP_OK);
    if (w + len + 2u >= cap) break;
    if (i) out[w++] = ' ';
    memcpy(out + w, key, len);
    w += len;
    out[w] = '\0';
  }
}

static fbs_goap_request mk_request(const fbs_goap_state *start, const fbs_goap_cond *goal,
                                   size_t goal_len, int heuristic) {
  fbs_goap_request req;
  req.start = start;
  req.goal = goal;
  req.goal_len = goal_len;
  req.heuristic = heuristic;
  req.max_nodes = 0u;
  req.max_depth = 0u;
  req.cost_override = NULL;
  req.proc_pre = NULL;
  req.user = NULL;
  return req;
}

static unsigned char *serialize_alloc(const fbs_goap_domain *d, size_t *out_len) {
  size_t need = fbs_goap_domain_serialized_size(d);
  size_t written = 0;
  unsigned char *buf = (unsigned char *)malloc(need ? need : 1u);
  CHECK(buf != NULL);
  CHECK(fbs_goap_domain_serialize(d, buf, need, &written) == FBS_GOAP_OK);
  CHECK(written == need);
  *out_len = need;
  return buf;
}

/* ------------------------------------------------------------------------- */
/* The GPGOAP soldier domain (T-1), from README.md:29-35 of                  */
/* https://github.com/stolk/GPGOAP. Unit costs; both plans below are         */
/* hand-computed and both appear in that README, so a disagreement is a      */
/* real signal.                                                              */
/* ------------------------------------------------------------------------- */

typedef struct {
  fbs_goap_domain *d;
  fbs_goap_atom enemyvisible, armedwithgun, weaponloaded, enemylinedup;
  fbs_goap_atom enemyalive, armedwithbomb, nearenemy, alive;
  fbs_goap_action scout, approach, aim, shoot, load, detonate, flee;
} soldier;

/* with_shoot / with_detonate remove the two enemy-killing actions (T-2);
 * reverse adds every row in reverse registration order (T-6b). */
static void soldier_build(soldier *s, int with_shoot, int with_detonate, int reverse) {
  fbs_goap_cond pre[2];
  fbs_goap_effect eff[2];

  s->d = make_domain();
  s->enemyvisible = atom_add(s->d, "enemyvisible", 0, 1, 0);
  s->armedwithgun = atom_add(s->d, "armedwithgun", 0, 1, 0);
  s->weaponloaded = atom_add(s->d, "weaponloaded", 0, 1, 0);
  s->enemylinedup = atom_add(s->d, "enemylinedup", 0, 1, 0);
  s->enemyalive = atom_add(s->d, "enemyalive", 0, 1, 0);
  s->armedwithbomb = atom_add(s->d, "armedwithbomb", 0, 1, 0);
  s->nearenemy = atom_add(s->d, "nearenemy", 0, 1, 0);
  s->alive = atom_add(s->d, "alive", 0, 1, 0);

  s->scout = action_add(s->d, "scout", 1);
  pre[0] = mk_cond(s->armedwithgun, FBS_GOAP_EQ, 1);
  add_pres(s->d, s->scout, pre, 1u, reverse);
  eff[0] = mk_effect(s->enemyvisible, FBS_GOAP_SET, 1);
  add_effs(s->d, s->scout, eff, 1u, reverse);

  s->approach = action_add(s->d, "approach", 1);
  pre[0] = mk_cond(s->enemyvisible, FBS_GOAP_EQ, 1);
  add_pres(s->d, s->approach, pre, 1u, reverse);
  eff[0] = mk_effect(s->nearenemy, FBS_GOAP_SET, 1);
  add_effs(s->d, s->approach, eff, 1u, reverse);

  s->aim = action_add(s->d, "aim", 1);
  pre[0] = mk_cond(s->enemyvisible, FBS_GOAP_EQ, 1);
  pre[1] = mk_cond(s->weaponloaded, FBS_GOAP_EQ, 1);
  add_pres(s->d, s->aim, pre, 2u, reverse);
  eff[0] = mk_effect(s->enemylinedup, FBS_GOAP_SET, 1);
  add_effs(s->d, s->aim, eff, 1u, reverse);

  s->shoot = FBS_GOAP_ACTION_NONE;
  if (with_shoot) {
    s->shoot = action_add(s->d, "shoot", 1);
    pre[0] = mk_cond(s->enemylinedup, FBS_GOAP_EQ, 1);
    add_pres(s->d, s->shoot, pre, 1u, reverse);
    eff[0] = mk_effect(s->enemyalive, FBS_GOAP_SET, 0);
    add_effs(s->d, s->shoot, eff, 1u, reverse);
  }

  s->load = action_add(s->d, "load", 1);
  pre[0] = mk_cond(s->armedwithgun, FBS_GOAP_EQ, 1);
  add_pres(s->d, s->load, pre, 1u, reverse);
  eff[0] = mk_effect(s->weaponloaded, FBS_GOAP_SET, 1);
  add_effs(s->d, s->load, eff, 1u, reverse);

  s->detonate = FBS_GOAP_ACTION_NONE;
  if (with_detonate) {
    s->detonate = action_add(s->d, "detonatebomb", 1);
    pre[0] = mk_cond(s->armedwithbomb, FBS_GOAP_EQ, 1);
    pre[1] = mk_cond(s->nearenemy, FBS_GOAP_EQ, 1);
    add_pres(s->d, s->detonate, pre, 2u, reverse);
    eff[0] = mk_effect(s->alive, FBS_GOAP_SET, 0);
    eff[1] = mk_effect(s->enemyalive, FBS_GOAP_SET, 0);
    add_effs(s->d, s->detonate, eff, 2u, reverse);
  }

  s->flee = action_add(s->d, "flee", 1);
  pre[0] = mk_cond(s->enemyvisible, FBS_GOAP_EQ, 1);
  add_pres(s->d, s->flee, pre, 1u, reverse);
  eff[0] = mk_effect(s->nearenemy, FBS_GOAP_SET, 0);
  add_effs(s->d, s->flee, eff, 1u, reverse);

  CHECK(fbs_goap_domain_seal(s->d) == FBS_GOAP_OK);
}

static fbs_goap_state *soldier_start(const soldier *s, state_buf *b) {
  fbs_goap_state *st = state_new(s->d, b);
  state_put(s->d, st, s->enemyvisible, 0);
  state_put(s->d, st, s->armedwithgun, 1);
  state_put(s->d, st, s->weaponloaded, 0);
  state_put(s->d, st, s->enemylinedup, 0);
  state_put(s->d, st, s->enemyalive, 1);
  state_put(s->d, st, s->armedwithbomb, 1);
  state_put(s->d, st, s->nearenemy, 0);
  state_put(s->d, st, s->alive, 1);
  return st;
}

/* ------------------------------------------------------------------------- */
/* T-1 — solvable, optimal plan, execution order                             */
/* ------------------------------------------------------------------------- */

static void test_t1_soldier_plans(void) {
  soldier s;
  state_buf sb;
  fbs_goap_state *start;
  fbs_goap_planner *p = NULL;
  fbs_goap_action plan[8];
  fbs_goap_result res;
  fbs_goap_cond goal[2];
  fbs_goap_request req;
  char keys[128];
  int h;

  soldier_build(&s, 1, 1, 0);
  start = soldier_start(&s, &sb);
  CHECK(fbs_goap_planner_create(s.d, NULL, NULL, &p) == FBS_GOAP_OK);

  /* Both heuristics must agree: h = 0 is optimal by construction. */
  for (h = 0; h < 2; ++h) {
    goal[0] = mk_cond(s.enemyalive, FBS_GOAP_EQ, 0);
    req = mk_request(start, goal, 1u, h ? FBS_GOAP_H_MAX_UNSAT : FBS_GOAP_H_ZERO);
    memset(plan, 0, sizeof plan);
    CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_FOUND);
    CHECK(res.plan_len == 3u);
    CHECK(res.plan_cost == 3);
    CHECK(plan[0] == s.scout); /* execution order, fixing G-15 */
    plan_to_keys(s.d, plan, res.plan_len, keys, sizeof keys);
    CHECK(strcmp(keys, "scout approach detonatebomb") == 0);
    CHECK(res.nodes_expanded > 0u);
    CHECK(res.nodes_generated > 0u);
    CHECK(res.peak_open > 0u);

    /* the plan really executes and really reaches the goal */
    {
      size_t first_invalid = 99u;
      int met = 0;
      CHECK(fbs_goap_plan_validate(p, start, plan, res.plan_len, goal, 1u, NULL, NULL,
                                   &first_invalid, &met) == FBS_GOAP_OK);
      CHECK(first_invalid == res.plan_len);
      CHECK(met == 1);
    }

    /* add alive == 1 and the suicide plan is no longer available */
    goal[1] = mk_cond(s.alive, FBS_GOAP_EQ, 1);
    req = mk_request(start, goal, 2u, h ? FBS_GOAP_H_MAX_UNSAT : FBS_GOAP_H_ZERO);
    memset(plan, 0, sizeof plan);
    CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_FOUND);
    CHECK(res.plan_len == 4u);
    CHECK(res.plan_cost == 4);
    plan_to_keys(s.d, plan, res.plan_len, keys, sizeof keys);
    CHECK(strcmp(keys, "scout load aim shoot") == 0);
    {
      size_t first_invalid = 99u;
      int met = 0;
      CHECK(fbs_goap_plan_validate(p, start, plan, res.plan_len, goal, 2u, NULL, NULL,
                                   &first_invalid, &met) == FBS_GOAP_OK);
      CHECK(first_invalid == res.plan_len);
      CHECK(met == 1);
    }
  }

  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(s.d);
}

/* ------------------------------------------------------------------------- */
/* T-2 — unsolvable is proven, and never confused with the node cap (G-4)    */
/* ------------------------------------------------------------------------- */

static void test_t2_unsolvable_vs_node_cap(void) {
  soldier s;
  state_buf sb;
  fbs_goap_state *start;
  fbs_goap_planner *p = NULL;
  fbs_goap_action plan[8];
  fbs_goap_result res;
  fbs_goap_cond goal[1];
  fbs_goap_request req;

  soldier_build(&s, 0, 0, 0); /* no shoot, no detonatebomb */
  start = soldier_start(&s, &sb);
  CHECK(fbs_goap_planner_create(s.d, NULL, NULL, &p) == FBS_GOAP_OK);

  goal[0] = mk_cond(s.enemyalive, FBS_GOAP_EQ, 0);
  req = mk_request(start, goal, 1u, FBS_GOAP_H_ZERO);
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_UNSOLVABLE); /* proven, not timed out */
  CHECK(res.plan_len == 0u);
  CHECK(res.plan_cost == 0);
  CHECK(res.nodes_expanded < 4096u); /* strictly inside the default cap */
  CHECK(res.nodes_expanded > 0u);

  /* the same domain with a one-expansion budget is NODE_CAP, never UNSOLVABLE */
  req.max_nodes = 1u;
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_NODE_CAP);
  CHECK(res.plan_len == 0u);
  CHECK(res.nodes_expanded == 1u);

  /* H_MAX_UNSAT proves the same thing */
  req.max_nodes = 0u;
  req.heuristic = FBS_GOAP_H_MAX_UNSAT;
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_UNSOLVABLE);

  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(s.d);
}

/* ------------------------------------------------------------------------- */
/* T-3 — a longer cheaper plan beats a shorter expensive one (G-6/G-7)       */
/* ------------------------------------------------------------------------- */

/* goal g is reachable by bigLeap (cost 10) or stepA+stepB+stepC (2 each). */
static fbs_goap_domain *build_steps(int with_big_leap, fbs_goap_atom *out_goal) {
  fbs_goap_domain *d = make_domain();
  fbs_goap_atom a = atom_add(d, "a", 0, 1, 0);
  fbs_goap_atom b = atom_add(d, "b", 0, 1, 0);
  fbs_goap_atom g = atom_add(d, "g", 0, 1, 0);
  fbs_goap_action act;

  if (with_big_leap) {
    act = action_add(d, "bigLeap", 10);
    CHECK(fbs_goap_action_effect(d, act, g, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
  }
  act = action_add(d, "stepA", 2);
  CHECK(fbs_goap_action_effect(d, act, a, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
  act = action_add(d, "stepB", 2);
  CHECK(fbs_goap_action_pre(d, act, a, FBS_GOAP_EQ, 1) == FBS_GOAP_OK);
  CHECK(fbs_goap_action_effect(d, act, b, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
  act = action_add(d, "stepC", 2);
  CHECK(fbs_goap_action_pre(d, act, b, FBS_GOAP_EQ, 1) == FBS_GOAP_OK);
  CHECK(fbs_goap_action_effect(d, act, g, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
  CHECK(fbs_goap_domain_seal(d) == FBS_GOAP_OK);
  *out_goal = g;
  return d;
}

static void test_t3_cost_preference(void) {
  fbs_goap_atom g;
  fbs_goap_domain *d = build_steps(1, &g);
  state_buf sb;
  fbs_goap_state *start = state_new_defaults(d, &sb);
  fbs_goap_planner *p = NULL;
  fbs_goap_action plan[8];
  fbs_goap_result res;
  fbs_goap_cond goal[1];
  fbs_goap_request req;
  char keys[128];
  int h;

  CHECK(fbs_goap_planner_create(d, NULL, NULL, &p) == FBS_GOAP_OK);
  goal[0] = mk_cond(g, FBS_GOAP_EQ, 1);
  for (h = 0; h < 2; ++h) {
    req = mk_request(start, goal, 1u, h ? FBS_GOAP_H_MAX_UNSAT : FBS_GOAP_H_ZERO);
    CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_FOUND);
    CHECK(res.plan_len == 3u);
    CHECK(res.plan_cost == 6); /* a counting heuristic would return bigLeap here */
    plan_to_keys(d, plan, res.plan_len, keys, sizeof keys);
    CHECK(strcmp(keys, "stepA stepB stepC") == 0);
  }

  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(d);
}

/* ------------------------------------------------------------------------- */
/* T-4 — replanning from a changed state, and per-agent costs (G-12)         */
/* ------------------------------------------------------------------------- */

static void test_t4_replanning(void) {
  soldier s;
  state_buf sb;
  fbs_goap_state *start;
  fbs_goap_planner *p = NULL;
  fbs_goap_action plan[8], plan2[8];
  fbs_goap_result res;
  fbs_goap_cond goal[1];
  fbs_goap_request req;
  size_t first_invalid = 99u;
  int met = 0;
  char keys[128];

  soldier_build(&s, 1, 1, 0);
  start = soldier_start(&s, &sb);
  CHECK(fbs_goap_planner_create(s.d, NULL, NULL, &p) == FBS_GOAP_OK);
  goal[0] = mk_cond(s.enemyalive, FBS_GOAP_EQ, 0);
  req = mk_request(start, goal, 1u, FBS_GOAP_H_ZERO);
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_FOUND);
  CHECK(res.plan_len == 3u);

  /* execute step 0, then corrupt the world so its promised effect did not
   * materialise: the tail is no longer executable at its very first step */
  CHECK(fbs_goap_apply(s.d, start, plan[0]) == FBS_GOAP_OK);
  CHECK(fbs_goap_state_known(s.d, start, s.enemyvisible) == 1);
  CHECK(fbs_goap_state_unset(s.d, start, s.enemyvisible) == FBS_GOAP_OK);
  CHECK(fbs_goap_state_known(s.d, start, s.enemyvisible) == 0);
  CHECK(fbs_goap_plan_validate(p, start, plan + 1, 2u, goal, 1u, NULL, NULL, &first_invalid,
                               &met) == FBS_GOAP_OK);
  CHECK(first_invalid == 0u); /* approach needs enemyvisible, which is unknown */
  CHECK(met == 0);

  /* replan from the actual state: valid, optimal, and not the old tail */
  CHECK(fbs_goap_plan(p, &req, plan2, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_FOUND);
  CHECK(res.plan_len == 3u);
  CHECK(res.plan_cost == 3);
  plan_to_keys(s.d, plan2, res.plan_len, keys, sizeof keys);
  CHECK(strcmp(keys, "scout approach detonatebomb") == 0);
  CHECK(!(res.plan_len == 2u && memcmp(plan2, plan + 1, 2u * sizeof plan[0]) == 0));
  CHECK(memcmp(plan2, plan + 1, 2u * sizeof plan[0]) != 0);
  first_invalid = 99u;
  CHECK(fbs_goap_plan_validate(p, start, plan2, res.plan_len, goal, 1u, NULL, NULL, &first_invalid,
                               &met) == FBS_GOAP_OK);
  CHECK(first_invalid == res.plan_len);
  CHECK(met == 1);

  /* two agents, one const domain, two cost_override arrays, two plans */
  {
    fbs_goap_cost cheap[8];
    fbs_goap_cost bomber[8];
    unsigned i, n = fbs_goap_action_count(s.d);
    state_buf fresh_buf;
    fbs_goap_state *fresh = soldier_start(&s, &fresh_buf);
    CHECK(n <= 8u);
    for (i = 0u; i < n; ++i) {
      cheap[i] = 1;
      bomber[i] = 1;
    }
    cheap[s.detonate] = 10; /* a demolition-shy agent shoots instead */
    bomber[s.shoot] = 10;   /* a marksman-shy agent detonates instead */

    req = mk_request(fresh, goal, 1u, FBS_GOAP_H_ZERO);
    req.cost_override = cheap;
    CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_FOUND);
    plan_to_keys(s.d, plan, res.plan_len, keys, sizeof keys);
    CHECK(strcmp(keys, "scout load aim shoot") == 0);
    CHECK(res.plan_cost == 4);

    req.cost_override = bomber;
    CHECK(fbs_goap_plan(p, &req, plan2, 8u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_FOUND);
    plan_to_keys(s.d, plan2, res.plan_len, keys, sizeof keys);
    CHECK(strcmp(keys, "scout approach detonatebomb") == 0);
    CHECK(res.plan_cost == 3);

    /* and the heuristic stays admissible under an override */
    req.heuristic = FBS_GOAP_H_MAX_UNSAT;
    req.cost_override = cheap;
    CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_FOUND);
    CHECK(res.plan_cost == 4);
  }

  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(s.d);
}

/* ------------------------------------------------------------------------- */
/* T-5 — bounded search always returns a detectable status                   */
/* ------------------------------------------------------------------------- */

/* n independent toggles: the reachable space is 2^n. */
static fbs_goap_domain *build_toggles(unsigned n) {
  fbs_goap_domain *d = NULL;
  fbs_goap_config cfg = fbs_goap_config_default();
  unsigned i;
  cfg.max_atoms = n;
  cfg.max_actions = n;
  cfg.max_conditions = 0u;
  cfg.max_effects = n;
  CHECK(fbs_goap_domain_create(&cfg, NULL, &d) == FBS_GOAP_OK);
  for (i = 0u; i < n; ++i) {
    char key[24];
    fbs_goap_atom a;
    fbs_goap_action act;
    sprintf(key, "t%u", i);
    a = atom_add(d, key, 0, 1, 0);
    sprintf(key, "set%u", i);
    act = action_add(d, key, 1);
    CHECK(fbs_goap_action_effect(d, act, a, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
  }
  CHECK(fbs_goap_domain_seal(d) == FBS_GOAP_OK);
  return d;
}

static void test_t5_bounded_search(void) {
  fbs_goap_domain *d = build_toggles(14u);
  state_buf sb;
  fbs_goap_state *start = state_new_defaults(d, &sb);
  fbs_goap_planner *p = NULL;
  fbs_goap_planner_config pcfg;
  fbs_goap_action plan[32];
  fbs_goap_result res;
  fbs_goap_cond goal[14];
  fbs_goap_request req;
  unsigned i;

  for (i = 0u; i < 14u; ++i) goal[i] = mk_cond((fbs_goap_atom)i, FBS_GOAP_EQ, 1);
  CHECK(fbs_goap_planner_create(d, NULL, NULL, &p) == FBS_GOAP_OK);

  req = mk_request(start, goal, 14u, FBS_GOAP_H_ZERO);
  req.max_nodes = 64u;
  CHECK(fbs_goap_plan(p, &req, plan, 32u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_NODE_CAP);
  CHECK(res.plan_len == 0u);
  CHECK(res.plan_cost == 0);
  CHECK(res.nodes_expanded == 64u);
  CHECK(res.nodes_generated > 0u);
  CHECK(res.peak_open > 0u);

  /* max_nodes == 0 is the planner's capacity, never "no limit" */
  pcfg = fbs_goap_planner_config_default();
  pcfg.max_nodes = 32u;
  pcfg.max_depth = 64u;
  {
    fbs_goap_planner *small = NULL;
    CHECK(fbs_goap_planner_create(d, &pcfg, NULL, &small) == FBS_GOAP_OK);
    req.max_nodes = 0u;
    CHECK(fbs_goap_plan(small, &req, plan, 32u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_NODE_CAP);
    CHECK(res.nodes_expanded <= 32u);
    /* a request beyond the planner's capacity is rejected outright */
    req.max_nodes = 33u;
    CHECK(fbs_goap_plan(small, &req, plan, 32u, &res) == FBS_GOAP_E_INVALID);
    fbs_goap_planner_destroy(small);
  }

  /* The default 4096-node planner cannot even hold this space, and says so
   * rather than pretending: 2^14 states all sit at f < 14 under unit costs. */
  req.max_nodes = 0u;
  CHECK(fbs_goap_plan(p, &req, plan, 32u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_NODE_CAP);
  CHECK(res.plan_len == 0u);

  /* Given a budget that fits the whole reachable space, the same request is
   * FOUND with the 14-step plan: the cap was the only thing in the way. */
  {
    fbs_goap_planner *big = NULL;
    pcfg = fbs_goap_planner_config_default();
    pcfg.max_nodes = 20000u;
    pcfg.max_depth = 64u;
    CHECK(fbs_goap_planner_create(d, &pcfg, NULL, &big) == FBS_GOAP_OK);
    CHECK(fbs_goap_plan(big, &req, plan, 32u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_FOUND);
    CHECK(res.plan_len == 14u);
    CHECK(res.plan_cost == 14);
    CHECK(res.nodes_generated == 16383u); /* every state but the start */
    fbs_goap_planner_destroy(big);
  }

  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(d);

  /* depth cap: the only solution is three steps, the cap is two */
  {
    fbs_goap_atom g;
    fbs_goap_domain *steps = build_steps(0, &g);
    state_buf b2;
    fbs_goap_state *st = state_new_defaults(steps, &b2);
    fbs_goap_cond goal1[1];
    fbs_goap_planner *sp = NULL;
    goal1[0] = mk_cond(g, FBS_GOAP_EQ, 1);
    CHECK(fbs_goap_planner_create(steps, NULL, NULL, &sp) == FBS_GOAP_OK);
    req = mk_request(st, goal1, 1u, FBS_GOAP_H_ZERO);
    req.max_depth = 2u;
    CHECK(fbs_goap_plan(sp, &req, plan, 32u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_DEPTH_CAP);
    CHECK(res.plan_len == 0u);
    req.max_depth = 3u;
    CHECK(fbs_goap_plan(sp, &req, plan, 32u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_FOUND);
    CHECK(res.plan_len == 3u);
    fbs_goap_planner_destroy(sp);
    fbs_goap_domain_destroy(steps);
  }
}

/* ------------------------------------------------------------------------- */
/* T-6 — determinism                                                         */
/* ------------------------------------------------------------------------- */

static void test_t6a_repeatable(void) {
  soldier s;
  state_buf sb;
  fbs_goap_state *start;
  fbs_goap_planner *p = NULL;
  fbs_goap_action plan[8], first[8];
  fbs_goap_result res, res0;
  fbs_goap_cond goal[2];
  fbs_goap_request req;
  int i;

  soldier_build(&s, 1, 1, 0);
  start = soldier_start(&s, &sb);
  CHECK(fbs_goap_planner_create(s.d, NULL, NULL, &p) == FBS_GOAP_OK);
  goal[0] = mk_cond(s.enemyalive, FBS_GOAP_EQ, 0);
  goal[1] = mk_cond(s.alive, FBS_GOAP_EQ, 1);
  req = mk_request(start, goal, 2u, FBS_GOAP_H_MAX_UNSAT);

  memset(first, 0, sizeof first);
  memset(&res0, 0, sizeof res0);
  for (i = 0; i < 100; ++i) {
    memset(plan, 0, sizeof plan);
    CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
    if (i == 0) {
      memcpy(first, plan, sizeof plan);
      res0 = res;
      CHECK(res.outcome == FBS_GOAP_FOUND);
    } else {
      CHECK(memcmp(plan, first, sizeof plan) == 0);
      CHECK(res.plan_len == res0.plan_len);
      CHECK(res.plan_cost == res0.plan_cost);
      CHECK(res.nodes_expanded == res0.nodes_expanded);
      CHECK(res.nodes_generated == res0.nodes_generated);
      CHECK(res.peak_open == res0.peak_open);
    }
  }

  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(s.d);
}

static void test_t6b_row_order_irrelevant(void) {
  soldier fwd, rev;
  state_buf b1, b2;
  fbs_goap_state *s1, *s2;
  fbs_goap_planner *p1 = NULL, *p2 = NULL;
  fbs_goap_action plan1[8], plan2[8];
  fbs_goap_result r1, r2;
  fbs_goap_cond goal[2];
  fbs_goap_request q1, q2;
  unsigned char *blob1, *blob2;
  size_t len1 = 0, len2 = 0;
  fbs_goap_cond rows[4];
  size_t n = 0;

  soldier_build(&fwd, 1, 1, 0);
  soldier_build(&rev, 1, 1, 1);

  blob1 = serialize_alloc(fwd.d, &len1);
  blob2 = serialize_alloc(rev.d, &len2);
  CHECK(len1 == len2);
  CHECK(len1 > 0u && memcmp(blob1, blob2, len1) == 0);

  /* and the canonical order is the documented one: (atom, cmp, value) */
  CHECK(fbs_goap_action_conditions(rev.d, rev.detonate, rows, 4u, &n) == FBS_GOAP_OK);
  CHECK(n == 2u);
  CHECK(rows[0].atom < rows[1].atom);
  CHECK(rows[0].atom == rev.armedwithbomb);
  CHECK(rows[1].atom == rev.nearenemy);

  s1 = soldier_start(&fwd, &b1);
  s2 = soldier_start(&rev, &b2);
  CHECK(fbs_goap_planner_create(fwd.d, NULL, NULL, &p1) == FBS_GOAP_OK);
  CHECK(fbs_goap_planner_create(rev.d, NULL, NULL, &p2) == FBS_GOAP_OK);
  goal[0] = mk_cond(fwd.enemyalive, FBS_GOAP_EQ, 0);
  goal[1] = mk_cond(fwd.alive, FBS_GOAP_EQ, 1);
  q1 = mk_request(s1, goal, 2u, FBS_GOAP_H_ZERO);
  q2 = mk_request(s2, goal, 2u, FBS_GOAP_H_ZERO);
  CHECK(fbs_goap_plan(p1, &q1, plan1, 8u, &r1) == FBS_GOAP_OK);
  CHECK(fbs_goap_plan(p2, &q2, plan2, 8u, &r2) == FBS_GOAP_OK);
  CHECK(r1.outcome == FBS_GOAP_FOUND && r2.outcome == FBS_GOAP_FOUND);
  CHECK(r1.plan_len == r2.plan_len);
  CHECK(r1.plan_cost == r2.plan_cost);
  CHECK(r1.nodes_expanded == r2.nodes_expanded);
  CHECK(memcmp(plan1, plan2, r1.plan_len * sizeof plan1[0]) == 0);

  free(blob1);
  free(blob2);
  fbs_goap_planner_destroy(p1);
  fbs_goap_planner_destroy(p2);
  fbs_goap_domain_destroy(fwd.d);
  fbs_goap_domain_destroy(rev.d);
}

/* A deliberate three-way f tie whose members have distinct g.
 *
 * atoms g1, g2 (goal rows), actions mk2 (cost 1, g2 := 1), mk1 (cost 5,
 * g1 := 1), both (cost 6, g1 := 1 and g2 := 1). cheapest[g1] = 5,
 * cheapest[g2] = 1, so expanding the start yields exactly three successors,
 * every one of them with f = 6:
 *
 *     mk2  -> g = 1, h = 5, seq 1
 *     mk1  -> g = 5, h = 1, seq 2
 *     both -> g = 6, h = 0, seq 3
 *
 * (f asc, g desc, seq asc) pops `both` first — the LAST of the three by seq —
 * so it is the g-descending rule, not the sequence rule, that decides. `both`
 * satisfies the goal, so the search stops having expanded the start and
 * nothing else: nodes_expanded == 1 is the witness. Cost 6 is optimal either
 * way (mk1 + mk2 also costs 6), so the plan is the only thing that differs. */
static void test_t6c_tie_order(void) {
  fbs_goap_domain *d = make_domain();
  fbs_goap_atom g1 = atom_add(d, "g1", 0, 1, 0);
  fbs_goap_atom g2 = atom_add(d, "g2", 0, 1, 0);
  fbs_goap_action mk2 = action_add(d, "mk2", 1);
  fbs_goap_action mk1 = action_add(d, "mk1", 5);
  fbs_goap_action both = action_add(d, "both", 6);
  state_buf sb;
  fbs_goap_state *start;
  fbs_goap_planner *p = NULL;
  fbs_goap_action plan[8];
  fbs_goap_result res;
  fbs_goap_cond goal[2];
  fbs_goap_request req;
  char keys[64];

  CHECK(fbs_goap_action_effect(d, mk2, g2, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
  CHECK(fbs_goap_action_effect(d, mk1, g1, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
  CHECK(fbs_goap_action_effect(d, both, g1, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
  CHECK(fbs_goap_action_effect(d, both, g2, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
  CHECK(fbs_goap_domain_seal(d) == FBS_GOAP_OK);

  start = state_new_defaults(d, &sb);
  CHECK(fbs_goap_planner_create(d, NULL, NULL, &p) == FBS_GOAP_OK);
  goal[0] = mk_cond(g1, FBS_GOAP_EQ, 1);
  goal[1] = mk_cond(g2, FBS_GOAP_EQ, 1);

  req = mk_request(start, goal, 2u, FBS_GOAP_H_MAX_UNSAT);
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_FOUND);
  CHECK(res.plan_len == 1u);
  CHECK(res.plan_cost == 6);
  CHECK(plan[0] == both);
  plan_to_keys(d, plan, res.plan_len, keys, sizeof keys);
  CHECK(strcmp(keys, "both") == 0);
  CHECK(res.nodes_expanded == 1u); /* only the start; the g-desc rule ended it */
  CHECK(res.nodes_generated == 3u);
  CHECK(res.peak_open == 3u);

  /* h = 0 collapses f to g, so the same three nodes pop in g order and the
   * search does more work for the identical, equally optimal answer */
  req.heuristic = FBS_GOAP_H_ZERO;
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_FOUND);
  CHECK(res.plan_cost == 6);
  CHECK(plan[0] == both);
  CHECK(res.nodes_expanded == 3u);

  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(d);

  /* The remaining tie is (f, g) equal: the insertion sequence decides, and
   * successors are generated in ascending action id, so winA wins. */
  {
    fbs_goap_domain *e = make_domain();
    fbs_goap_atom won = atom_add(e, "won", 0, 1, 0);
    fbs_goap_atom mark = atom_add(e, "mark", 0, 1, 0);
    fbs_goap_atom other = atom_add(e, "other", 0, 1, 0);
    fbs_goap_action a = action_add(e, "winA", 3);
    fbs_goap_action b = action_add(e, "winB", 3);
    state_buf eb;
    fbs_goap_state *es;
    fbs_goap_planner *ep = NULL;
    fbs_goap_cond eg[1];
    fbs_goap_request er;
    fbs_goap_result eres;
    fbs_goap_action eplan[4];

    CHECK(fbs_goap_action_effect(e, a, won, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
    CHECK(fbs_goap_action_effect(e, a, mark, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
    CHECK(fbs_goap_action_effect(e, b, won, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
    CHECK(fbs_goap_action_effect(e, b, other, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
    CHECK(fbs_goap_domain_seal(e) == FBS_GOAP_OK);
    es = state_new_defaults(e, &eb);
    CHECK(fbs_goap_planner_create(e, NULL, NULL, &ep) == FBS_GOAP_OK);
    eg[0] = mk_cond(won, FBS_GOAP_EQ, 1);
    er = mk_request(es, eg, 1u, FBS_GOAP_H_ZERO);
    CHECK(fbs_goap_plan(ep, &er, eplan, 4u, &eres) == FBS_GOAP_OK);
    CHECK(eres.outcome == FBS_GOAP_FOUND);
    CHECK(eres.plan_len == 1u);
    CHECK(eplan[0] == a);
    CHECK(eres.nodes_generated == 2u);
    fbs_goap_planner_destroy(ep);
    fbs_goap_domain_destroy(e);
  }
}

/* ------------------------------------------------------------------------- */
/* T-7 — numeric and enumerated state (criterion 1)                          */
/* ------------------------------------------------------------------------- */

static void test_t7_numeric_state(void) {
  fbs_goap_domain *d = make_domain();
  fbs_goap_atom wood = atom_add(d, "wood", 0, 10, 0);
  fbs_goap_action chop = action_add(d, "chop", 1);
  state_buf sb;
  fbs_goap_state *start;
  fbs_goap_planner *p = NULL;
  fbs_goap_action plan[32];
  fbs_goap_result res;
  fbs_goap_cond goal[1];
  fbs_goap_request req;
  int32_t v = 0;
  int h;

  CHECK(fbs_goap_action_effect(d, chop, wood, FBS_GOAP_ADD, 1) == FBS_GOAP_OK);
  CHECK(fbs_goap_domain_seal(d) == FBS_GOAP_OK);
  start = state_new_defaults(d, &sb);
  CHECK(fbs_goap_planner_create(d, NULL, NULL, &p) == FBS_GOAP_OK);

  for (h = 0; h < 2; ++h) {
    goal[0] = mk_cond(wood, FBS_GOAP_GE, 3);
    req = mk_request(start, goal, 1u, h ? FBS_GOAP_H_MAX_UNSAT : FBS_GOAP_H_ZERO);
    CHECK(fbs_goap_plan(p, &req, plan, 32u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_FOUND);
    CHECK(res.plan_len == 3u);
    CHECK(res.plan_cost == 3);
    CHECK(plan[0] == chop && plan[1] == chop && plan[2] == chop);

    /* ADD clamps at max_value, so "wood >= 11" is provably unreachable rather
     * than an infinite frontier */
    goal[0] = mk_cond(wood, FBS_GOAP_GE, 11);
    req = mk_request(start, goal, 1u, h ? FBS_GOAP_H_MAX_UNSAT : FBS_GOAP_H_ZERO);
    CHECK(fbs_goap_plan(p, &req, plan, 32u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_UNSOLVABLE);
    CHECK(res.nodes_expanded == 11u); /* exactly the 11 reachable states */
  }

  /* the clamp itself */
  {
    state_buf cb;
    fbs_goap_state *c = state_new_defaults(d, &cb);
    int i;
    for (i = 0; i < 20; ++i) CHECK(fbs_goap_apply(d, c, chop) == FBS_GOAP_OK);
    CHECK(fbs_goap_state_get(d, c, wood, &v) == FBS_GOAP_OK);
    CHECK(v == 10);
  }

  /* ADD on an UNKNOWN slot: the canonical zero an unknown slot holds is the
   * base, and the slot becomes known */
  {
    state_buf ub;
    fbs_goap_state *u = state_new(d, &ub);
    CHECK(fbs_goap_state_known(d, u, wood) == 0);
    CHECK(fbs_goap_apply(d, u, chop) == FBS_GOAP_OK);
    CHECK(fbs_goap_state_known(d, u, wood) == 1);
    CHECK(fbs_goap_state_get(d, u, wood, &v) == FBS_GOAP_OK);
    CHECK(v == 1);
  }

  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(d);

  /* all six comparators gate correctly, and an unknown slot satisfies none */
  {
    fbs_goap_domain *e = make_domain();
    fbs_goap_atom n = atom_add(e, "n", -5, 5, 0);
    state_buf eb;
    fbs_goap_state *s;
    fbs_goap_cond c[1];
    static const int cmps[6] = {FBS_GOAP_EQ, FBS_GOAP_NE, FBS_GOAP_LT,
                                FBS_GOAP_LE, FBS_GOAP_GT, FBS_GOAP_GE};
    /* expected[value + 5][cmp] against a threshold of 2 */
    int val, k;
    CHECK(fbs_goap_domain_seal(e) == FBS_GOAP_OK);
    s = state_new(e, &eb);
    for (k = 0; k < 6; ++k) {
      c[0] = mk_cond(n, cmps[k], 2);
      CHECK(fbs_goap_state_satisfies(e, s, c, 1u) == 0); /* unknown satisfies nothing */
    }
    for (val = -5; val <= 5; ++val) {
      CHECK(fbs_goap_state_set(e, s, n, (int32_t)val) == FBS_GOAP_OK);
      c[0] = mk_cond(n, FBS_GOAP_EQ, 2);
      CHECK(fbs_goap_state_satisfies(e, s, c, 1u) == (val == 2 ? 1 : 0));
      c[0] = mk_cond(n, FBS_GOAP_NE, 2);
      CHECK(fbs_goap_state_satisfies(e, s, c, 1u) == (val != 2 ? 1 : 0));
      c[0] = mk_cond(n, FBS_GOAP_LT, 2);
      CHECK(fbs_goap_state_satisfies(e, s, c, 1u) == (val < 2 ? 1 : 0));
      c[0] = mk_cond(n, FBS_GOAP_LE, 2);
      CHECK(fbs_goap_state_satisfies(e, s, c, 1u) == (val <= 2 ? 1 : 0));
      c[0] = mk_cond(n, FBS_GOAP_GT, 2);
      CHECK(fbs_goap_state_satisfies(e, s, c, 1u) == (val > 2 ? 1 : 0));
      c[0] = mk_cond(n, FBS_GOAP_GE, 2);
      CHECK(fbs_goap_state_satisfies(e, s, c, 1u) == (val >= 2 ? 1 : 0));
    }
    /* negative ADD clamps at min_value too */
    {
      fbs_goap_domain *f = make_domain();
      fbs_goap_atom hp = atom_add(f, "hp", 0, 30, 30);
      fbs_goap_action hit = action_add(f, "hit", 1);
      state_buf fb;
      fbs_goap_state *fs;
      int32_t got = 0;
      CHECK(fbs_goap_action_effect(f, hit, hp, FBS_GOAP_ADD, -20) == FBS_GOAP_OK);
      CHECK(fbs_goap_domain_seal(f) == FBS_GOAP_OK);
      fs = state_new_defaults(f, &fb);
      CHECK(fbs_goap_apply(f, fs, hit) == FBS_GOAP_OK);
      CHECK(fbs_goap_state_get(f, fs, hp, &got) == FBS_GOAP_OK);
      CHECK(got == 10);
      CHECK(fbs_goap_apply(f, fs, hit) == FBS_GOAP_OK);
      CHECK(fbs_goap_state_get(f, fs, hp, &got) == FBS_GOAP_OK);
      CHECK(got == 0);
      fbs_goap_domain_destroy(f);
    }
    fbs_goap_domain_destroy(e);
  }
}

/* An independent referee for the bounded-depth cases: exhaustive enumeration of
 * every action sequence of length <= depth_left, minimum cost wins. No heap, no
 * heuristic, no node identity — nothing the planner could be wrong about in the
 * same way. */
typedef struct {
  const fbs_goap_domain *d;
  const fbs_goap_cond *goal;
  size_t goal_len;
  fbs_goap_cost costs[8];
  unsigned actions;
  size_t state_size;
  fbs_goap_cost best;
  int failed;
} bf_ctx;

static void bf_search(bf_ctx *c, const fbs_goap_state *s, unsigned depth_left, fbs_goap_cost g,
                      state_buf *scratch, unsigned level) {
  unsigned act;
  int sat = fbs_goap_state_satisfies(c->d, s, c->goal, c->goal_len);
  if (sat < 0) {
    c->failed = 1;
    return;
  }
  if (sat == 1) {
    if (g < c->best) c->best = g; /* extending a reached goal can only cost more */
    return;
  }
  if (depth_left == 0u) return;
  for (act = 0u; act < c->actions; ++act) {
    fbs_goap_state *child;
    int ok = fbs_goap_action_applicable(c->d, s, (fbs_goap_action)act);
    if (ok < 0) {
      c->failed = 1;
      return;
    }
    if (ok == 0) continue;
    if (g + c->costs[act] >= c->best) continue; /* branch and bound */
    memcpy(scratch[level].w, s, c->state_size);
    child = (fbs_goap_state *)(void *)scratch[level].w;
    if (fbs_goap_apply(c->d, child, (fbs_goap_action)act) != FBS_GOAP_OK) {
      c->failed = 1;
      return;
    }
    bf_search(c, child, depth_left - 1u, (fbs_goap_cost)(g + c->costs[act]), scratch, level + 1u);
  }
}

/* FBS_GOAP_COST_MAX when no plan of length <= depth exists. */
static fbs_goap_cost brute_force_best(const fbs_goap_domain *d, const fbs_goap_state *start,
                                      const fbs_goap_cond *goal, size_t goal_len,
                                      const fbs_goap_cost *costs, unsigned depth) {
  bf_ctx c;
  state_buf scratch[8];
  unsigned i;
  c.d = d;
  c.goal = goal;
  c.goal_len = goal_len;
  c.actions = fbs_goap_action_count(d);
  c.state_size = fbs_goap_state_size(d);
  c.best = FBS_GOAP_COST_MAX;
  c.failed = 0;
  CHECK(c.actions <= 8u);
  CHECK(depth < 8u);
  for (i = 0u; i < c.actions && i < 8u; ++i) {
    c.costs[i] = 1;
    if (costs)
      c.costs[i] = costs[i];
    else
      CHECK(fbs_goap_action_cost(d, (fbs_goap_action)i, &c.costs[i]) == FBS_GOAP_OK);
  }
  bf_search(&c, start, depth, 0, scratch, 0u);
  CHECK(c.failed == 0);
  return c.best;
}

/* ------------------------------------------------------------------------- */
/* GOAP-1 (review) — the depth cap is sound AND complete                     */
/* ------------------------------------------------------------------------- */

/* The reviewer's case A2, verbatim. `A` and `B,C` reach the identical state
 * {s=1,t=0}: `A` in one step for 5, `B,C` in two steps for 2. With node
 * identity on the state alone, the cheap two-step arrival overwrote the depth
 * of the one-step arrival, the state was then discarded unexpanded under
 * max_depth = 2, and the planner answered `D` (one step, cost 8) — or, with
 * `D` removed, DEPTH_CAP — although `A,G` fits the cap at cost 6. With nodes
 * identified by (state, depth) both arrivals are live nodes and the answer is
 * optimal among plans of length <= max_depth. */
static void test_goap1_depth_cap_optimality(void) {
  int with_d;
  for (with_d = 1; with_d >= 0; --with_d) {
    fbs_goap_domain *dom = make_domain();
    fbs_goap_atom s = atom_add(dom, "s", 0, 1, 0);
    fbs_goap_atom t = atom_add(dom, "t", 0, 1, 0);
    fbs_goap_atom g = atom_add(dom, "g", 0, 1, 0);
    fbs_goap_action a = action_add(dom, "A", 5);
    fbs_goap_action b = action_add(dom, "B", 1);
    fbs_goap_action c = action_add(dom, "C", 1);
    fbs_goap_action gg = action_add(dom, "G", 1);
    fbs_goap_action dd = FBS_GOAP_ACTION_NONE;
    state_buf sb;
    fbs_goap_state *start;
    fbs_goap_planner *p = NULL;
    fbs_goap_action plan[8];
    fbs_goap_result res;
    fbs_goap_cond goal[1];
    fbs_goap_request req;
    char keys[64];
    int h;

    CHECK(fbs_goap_action_effect(dom, a, s, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
    CHECK(fbs_goap_action_effect(dom, b, t, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
    CHECK(fbs_goap_action_pre(dom, c, t, FBS_GOAP_EQ, 1) == FBS_GOAP_OK);
    CHECK(fbs_goap_action_effect(dom, c, s, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
    CHECK(fbs_goap_action_effect(dom, c, t, FBS_GOAP_SET, 0) == FBS_GOAP_OK);
    CHECK(fbs_goap_action_pre(dom, gg, s, FBS_GOAP_EQ, 1) == FBS_GOAP_OK);
    CHECK(fbs_goap_action_effect(dom, gg, g, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
    if (with_d) {
      dd = action_add(dom, "D", 8);
      CHECK(fbs_goap_action_effect(dom, dd, g, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
    }
    CHECK(fbs_goap_domain_seal(dom) == FBS_GOAP_OK);
    start = state_new_defaults(dom, &sb);
    CHECK(fbs_goap_planner_create(dom, NULL, NULL, &p) == FBS_GOAP_OK);
    goal[0] = mk_cond(g, FBS_GOAP_EQ, 1);

    for (h = 0; h < 2; ++h) {
      int heur = h ? FBS_GOAP_H_MAX_UNSAT : FBS_GOAP_H_ZERO;

      /* unbounded depth: the cheap three-step route wins */
      req = mk_request(start, goal, 1u, heur);
      CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
      CHECK(res.outcome == FBS_GOAP_FOUND);
      CHECK(res.plan_len == 3u);
      CHECK(res.plan_cost == 3);
      plan_to_keys(dom, plan, res.plan_len, keys, sizeof keys);
      CHECK(strcmp(keys, "B C G") == 0);

      /* max_depth 2: the best plan of length <= 2 is A,G at cost 6 — never D
       * at cost 8, and never DEPTH_CAP */
      req.max_depth = 2u;
      CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
      CHECK(res.outcome == FBS_GOAP_FOUND);
      CHECK(res.plan_len == 2u);
      CHECK(res.plan_cost == 6);
      plan_to_keys(dom, plan, res.plan_len, keys, sizeof keys);
      CHECK(strcmp(keys, "A G") == 0);

      /* max_depth 1: only D fits, so with D it is the answer and without it
       * there is genuinely no plan of that length */
      req.max_depth = 1u;
      CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
      if (with_d) {
        CHECK(res.outcome == FBS_GOAP_FOUND);
        CHECK(res.plan_len == 1u);
        CHECK(res.plan_cost == 8);
        CHECK(plan[0] == dd);
      } else {
        CHECK(res.outcome == FBS_GOAP_DEPTH_CAP);
        CHECK(res.plan_len == 0u);
      }

      /* max_depth 3 restores the optimum */
      req.max_depth = 3u;
      CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
      CHECK(res.outcome == FBS_GOAP_FOUND);
      CHECK(res.plan_cost == 3);

      /* and every cap agrees with exhaustive enumeration of that length */
      {
        unsigned cap;
        for (cap = 1u; cap <= 5u; ++cap) {
          fbs_goap_cost brute = brute_force_best(dom, start, goal, 1u, NULL, cap);
          req.max_depth = cap;
          CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
          if (brute == FBS_GOAP_COST_MAX) {
            CHECK(res.outcome == FBS_GOAP_DEPTH_CAP || res.outcome == FBS_GOAP_UNSOLVABLE);
          } else {
            CHECK(res.outcome == FBS_GOAP_FOUND);
            CHECK(res.plan_cost == brute);
            CHECK(res.plan_len <= (size_t)cap);
          }
        }
      }
      req.max_depth = 0u;
    }

    fbs_goap_planner_destroy(p);
    fbs_goap_domain_destroy(dom);
  }
}

/* ------------------------------------------------------------------------- */
/* T-8 — heuristic admissibility over pseudo-random domains                  */
/* ------------------------------------------------------------------------- */

/* 200 domains from the fixed xorshift seed 0x51ED2701. Every domain is small
 * enough (4 atoms of 3 values = 81 reachable states) that both searches always
 * terminate with a proof inside the caps, so any disagreement in outcome or
 * cost is proof that H_MAX_UNSAT is inadmissible.
 *
 * Every rng_below() sits alone in its own statement. Two draws inside one
 * argument list would be evaluated in an unspecified order, which made the
 * corpus differ between gcc and clang (review finding GOAP-4); the fix is
 * mechanical and the check count is now identical under both compilers.
 *
 * Each round is also planned under a random depth cap and refereed by
 * brute_force_best(), which enumerates every sequence of that length: FOUND
 * must carry exactly the enumerated optimum, and DEPTH_CAP/UNSOLVABLE must mean
 * the enumeration found nothing. That is the bounded-depth completeness the
 * amended header promises. */
static void test_t8_heuristic_admissibility(void) {
  int round;
  int found = 0, unsolvable = 0, bounded_found = 0, bounded_none = 0;

  rng_seed(0x51ED2701u);
  for (round = 0; round < 200; ++round) {
    fbs_goap_domain *d = make_domain();
    fbs_goap_atom atoms[4];
    fbs_goap_cond goal[2];
    state_buf sb;
    fbs_goap_state *start;
    fbs_goap_planner *p = NULL;
    fbs_goap_planner_config pcfg;
    fbs_goap_action plan_z[80], plan_m[80];
    fbs_goap_result rz, rm;
    fbs_goap_request req;
    unsigned na = 4u;
    unsigned nact, i, goal_len, cap_depth;

    nact = 2u + rng_below(5u);
    for (i = 0u; i < na; ++i) {
      char key[24];
      sprintf(key, "a%u", i);
      atoms[i] = atom_add(d, key, 0, 2, 0);
    }
    for (i = 0u; i < nact; ++i) {
      char key[24];
      fbs_goap_action act;
      unsigned npre, neff, j, cost;
      npre = rng_below(3u);
      neff = 1u + rng_below(2u);
      cost = 1u + rng_below(5u);
      sprintf(key, "op%u", i);
      act = action_add(d, key, (fbs_goap_cost)cost);
      for (j = 0u; j < npre; ++j) {
        fbs_goap_atom a;
        int cmp;
        int32_t v;
        a = atoms[rng_below(na)];
        cmp = (int)rng_below(6u);
        v = (int32_t)rng_below(3u);
        (void)fbs_goap_action_pre(d, act, a, cmp, v); /* duplicates are fine here */
      }
      for (j = 0u; j < neff; ++j) {
        fbs_goap_atom a;
        unsigned kind;
        a = atoms[rng_below(na)];
        kind = rng_below(2u);
        if (kind) {
          int32_t v = (int32_t)rng_below(3u);
          (void)fbs_goap_action_effect(d, act, a, FBS_GOAP_SET, v);
        } else {
          unsigned up = rng_below(2u);
          (void)fbs_goap_action_effect(d, act, a, FBS_GOAP_ADD, up ? 1 : -1);
        }
      }
    }
    CHECK(fbs_goap_domain_seal(d) == FBS_GOAP_OK);

    goal_len = 1u + rng_below(2u);
    for (i = 0u; i < goal_len; ++i) {
      fbs_goap_atom a;
      int cmp;
      int32_t v;
      a = atoms[rng_below(na)];
      cmp = (int)rng_below(6u);
      v = (int32_t)rng_below(3u);
      goal[i] = mk_cond(a, cmp, v);
    }
    cap_depth = 1u + rng_below(4u);

    start = state_new_defaults(d, &sb);
    pcfg = fbs_goap_planner_config_default();
    /* (state, depth) identity: at most 81 states x (cap + 1) depths */
    pcfg.max_nodes = 4096u;
    pcfg.max_depth = 128u;
    CHECK(fbs_goap_planner_create(d, &pcfg, NULL, &p) == FBS_GOAP_OK);

    req = mk_request(start, goal, goal_len, FBS_GOAP_H_ZERO);
    CHECK(fbs_goap_plan(p, &req, plan_z, 80u, &rz) == FBS_GOAP_OK);
    req.heuristic = FBS_GOAP_H_MAX_UNSAT;
    CHECK(fbs_goap_plan(p, &req, plan_m, 80u, &rm) == FBS_GOAP_OK);

    CHECK(rz.outcome != FBS_GOAP_NODE_CAP && rz.outcome != FBS_GOAP_DEPTH_CAP);
    CHECK(rm.outcome != FBS_GOAP_NODE_CAP && rm.outcome != FBS_GOAP_DEPTH_CAP);
    CHECK(rz.outcome == rm.outcome);
    CHECK(rz.plan_cost == rm.plan_cost); /* the admissibility assertion */
    if (rz.outcome == FBS_GOAP_FOUND) {
      size_t fi = 99u;
      int met = 0;
      ++found;
      CHECK(fbs_goap_plan_validate(p, start, plan_m, rm.plan_len, goal, goal_len, NULL, NULL, &fi,
                                   &met) == FBS_GOAP_OK);
      CHECK(fi == rm.plan_len);
      CHECK(met == 1);
      /* the heuristic never expands more than uniform cost search */
      CHECK(rm.nodes_expanded <= rz.nodes_expanded);
    } else if (rz.outcome == FBS_GOAP_UNSOLVABLE) {
      ++unsolvable;
    }

    /* the same request under a depth cap, refereed by exhaustive enumeration */
    {
      fbs_goap_cost brute = brute_force_best(d, start, goal, goal_len, NULL, cap_depth);
      int hh;
      for (hh = 0; hh < 2; ++hh) {
        fbs_goap_result rb;
        fbs_goap_action plan_b[80];
        req.heuristic = hh ? FBS_GOAP_H_MAX_UNSAT : FBS_GOAP_H_ZERO;
        req.max_depth = cap_depth;
        CHECK(fbs_goap_plan(p, &req, plan_b, 80u, &rb) == FBS_GOAP_OK);
        CHECK(rb.outcome != FBS_GOAP_NODE_CAP);
        if (brute == FBS_GOAP_COST_MAX) {
          /* no sequence of this length reaches the goal */
          CHECK(rb.outcome == FBS_GOAP_UNSOLVABLE || rb.outcome == FBS_GOAP_DEPTH_CAP);
          CHECK(rb.plan_len == 0u);
          if (hh == 0) ++bounded_none;
        } else {
          CHECK(rb.outcome == FBS_GOAP_FOUND || rb.outcome == FBS_GOAP_ALREADY_SATISFIED);
          CHECK(rb.plan_cost == brute); /* optimal among plans of length <= cap */
          CHECK(rb.plan_len <= (size_t)cap_depth);
          if (hh == 0) ++bounded_found;
        }
      }
      req.max_depth = 0u;
    }

    fbs_goap_planner_destroy(p);
    fbs_goap_domain_destroy(d);
  }
  /* the corpus is not degenerate: it contains both kinds of proof, unbounded
   * and bounded */
  CHECK(found > 20);
  CHECK(unsolvable > 5);
  CHECK(bounded_found > 20);
  CHECK(bounded_none > 5);
}

/* ------------------------------------------------------------------------- */
/* T-9 — cost validation and overflow (G-11)                                 */
/* ------------------------------------------------------------------------- */

static void test_t9_cost_validation(void) {
  fbs_goap_domain *d = make_domain();
  fbs_goap_atom x = atom_add(d, "x", 0, 4, 0);
  fbs_goap_action bump;
  fbs_goap_action tmp = FBS_GOAP_ACTION_NONE;
  state_buf sb;
  fbs_goap_state *start;
  fbs_goap_planner *p = NULL;
  fbs_goap_action plan[8];
  fbs_goap_result res;
  fbs_goap_cond goal[1];
  fbs_goap_request req;
  fbs_goap_cost over[4];
  unsigned i;

  CHECK(fbs_goap_action_add(d, "neg", 3u, -1, &tmp) == FBS_GOAP_E_RANGE);
  CHECK(tmp == FBS_GOAP_ACTION_NONE);
  CHECK(fbs_goap_action_add(d, "big", 3u, FBS_GOAP_COST_MAX + 1, &tmp) == FBS_GOAP_E_RANGE);
  CHECK(tmp == FBS_GOAP_ACTION_NONE);
  CHECK(fbs_goap_action_add(d, "min", 3u, 0, &tmp) == FBS_GOAP_OK);
  CHECK(fbs_goap_action_add(d, "max", 3u, FBS_GOAP_COST_MAX, &tmp) == FBS_GOAP_OK);
  CHECK(fbs_goap_action_count(d) == 2u);

  /* a plan whose path cost would pass FBS_GOAP_COST_MAX is E_RANGE, never a
   * wrapped or negative plan_cost */
  bump = action_add(d, "bump", FBS_GOAP_COST_MAX);
  CHECK(fbs_goap_action_effect(d, bump, x, FBS_GOAP_ADD, 1) == FBS_GOAP_OK);
  CHECK(fbs_goap_domain_seal(d) == FBS_GOAP_OK);
  start = state_new_defaults(d, &sb);
  CHECK(fbs_goap_planner_create(d, NULL, NULL, &p) == FBS_GOAP_OK);
  goal[0] = mk_cond(x, FBS_GOAP_GE, 3);
  req = mk_request(start, goal, 1u, FBS_GOAP_H_ZERO);
  memset(&res, 0xA5, sizeof res);
  memset(plan, 0xA5, sizeof plan);
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_E_RANGE);
  CHECK(untouched(&res, sizeof res, 0xA5));
  CHECK(untouched(plan, sizeof plan, 0xA5));

  /* a cost_override entry outside [0, COST_MAX] is E_RANGE before any search */
  for (i = 0u; i < fbs_goap_action_count(d); ++i) over[i] = 1;
  over[bump] = -1;
  req.cost_override = over;
  memset(&res, 0xA5, sizeof res);
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_E_RANGE);
  CHECK(untouched(&res, sizeof res, 0xA5));
  over[bump] = FBS_GOAP_COST_MAX + 1;
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_E_RANGE);
  CHECK(untouched(&res, sizeof res, 0xA5));

  /* and with a sane override the same domain plans normally */
  over[bump] = 2;
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_FOUND);
  CHECK(res.plan_len == 3u);
  CHECK(res.plan_cost == 6);

  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(d);

  /* range checks on atoms and effects */
  {
    fbs_goap_domain *e = make_domain();
    fbs_goap_atom a = FBS_GOAP_ATOM_NONE;
    fbs_goap_atom hp;
    fbs_goap_action act;
    CHECK(fbs_goap_atom_add(e, "bad", 3u, 5, 1, 3, &a) == FBS_GOAP_E_RANGE); /* min > max */
    CHECK(a == FBS_GOAP_ATOM_NONE);
    CHECK(fbs_goap_atom_add(e, "bad", 3u, 0, 10, 11, &a) == FBS_GOAP_E_RANGE); /* default outside */
    CHECK(fbs_goap_atom_add(e, "bad", 3u, 0, 10, -1, &a) == FBS_GOAP_E_RANGE);
    CHECK(a == FBS_GOAP_ATOM_NONE);
    hp = atom_add(e, "hp", 0, 30, 30);
    act = action_add(e, "act", 1);
    CHECK(fbs_goap_action_effect(e, act, hp, FBS_GOAP_SET, 31) == FBS_GOAP_E_RANGE);
    CHECK(fbs_goap_action_effect(e, act, hp, FBS_GOAP_SET, -1) == FBS_GOAP_E_RANGE);
    CHECK(fbs_goap_action_effect(e, act, hp, FBS_GOAP_ADD, -1000000) == FBS_GOAP_OK); /* clamps */
    /* conditions are NOT range checked: an unsatisfiable row is legitimate */
    CHECK(fbs_goap_action_pre(e, act, hp, FBS_GOAP_GT, 9999) == FBS_GOAP_OK);
    CHECK(fbs_goap_domain_seal(e) == FBS_GOAP_OK);
    fbs_goap_domain_destroy(e);
  }
}

/* ------------------------------------------------------------------------- */
/* T-10 — no globals, no shared state between domains or planners            */
/* ------------------------------------------------------------------------- */

static void test_t10_reentrancy(void) {
  soldier s;
  fbs_goap_atom g;
  fbs_goap_domain *steps;
  state_buf sb, tb;
  fbs_goap_state *ss, *ts;
  fbs_goap_planner *p1 = NULL, *p2 = NULL, *p3 = NULL;
  fbs_goap_action plan_a[8], plan_b[8], plan_c[8];
  fbs_goap_result ra, rb, rc, ra2, rb2;
  fbs_goap_cond goal_s[1], goal_t[1];
  fbs_goap_request qa, qb;

  /* two domains built interleaved */
  soldier_build(&s, 1, 1, 0);
  steps = build_steps(1, &g);
  ss = soldier_start(&s, &sb);
  ts = state_new_defaults(steps, &tb);
  goal_s[0] = mk_cond(s.enemyalive, FBS_GOAP_EQ, 0);
  goal_t[0] = mk_cond(g, FBS_GOAP_EQ, 1);

  CHECK(fbs_goap_planner_create(s.d, NULL, NULL, &p1) == FBS_GOAP_OK);
  CHECK(fbs_goap_planner_create(steps, NULL, NULL, &p2) == FBS_GOAP_OK);
  CHECK(fbs_goap_planner_create(s.d, NULL, NULL, &p3) == FBS_GOAP_OK);

  qa = mk_request(ss, goal_s, 1u, FBS_GOAP_H_ZERO);
  qb = mk_request(ts, goal_t, 1u, FBS_GOAP_H_ZERO);

  CHECK(fbs_goap_plan(p1, &qa, plan_a, 8u, &ra) == FBS_GOAP_OK);
  CHECK(fbs_goap_plan(p2, &qb, plan_b, 8u, &rb) == FBS_GOAP_OK);
  /* interleave: the second planner on the first domain must agree exactly */
  CHECK(fbs_goap_plan(p3, &qa, plan_c, 8u, &rc) == FBS_GOAP_OK);
  CHECK(fbs_goap_plan(p1, &qa, plan_a, 8u, &ra2) == FBS_GOAP_OK);
  CHECK(fbs_goap_plan(p2, &qb, plan_b, 8u, &rb2) == FBS_GOAP_OK);

  CHECK(ra.outcome == FBS_GOAP_FOUND && rb.outcome == FBS_GOAP_FOUND);
  CHECK(ra.plan_len == rc.plan_len && ra.plan_cost == rc.plan_cost);
  CHECK(ra.nodes_expanded == rc.nodes_expanded);
  CHECK(ra.nodes_generated == rc.nodes_generated);
  CHECK(ra.peak_open == rc.peak_open);
  CHECK(memcmp(plan_a, plan_c, ra.plan_len * sizeof plan_a[0]) == 0);
  CHECK(ra2.nodes_expanded == ra.nodes_expanded);
  CHECK(rb2.nodes_expanded == rb.nodes_expanded);
  CHECK(rb2.plan_cost == rb.plan_cost && rb.plan_cost == 6);

  /* the two planners hold their own memory */
  CHECK(fbs_goap_planner_memory(p1) > 0u);
  CHECK(fbs_goap_planner_memory(p1) == fbs_goap_planner_memory(p3));
  CHECK(fbs_goap_domain_memory(s.d) > 0u);

  fbs_goap_planner_destroy(p1);
  fbs_goap_planner_destroy(p2);
  fbs_goap_planner_destroy(p3);
  fbs_goap_domain_destroy(steps);
  fbs_goap_domain_destroy(s.d);
}

/* ------------------------------------------------------------------------- */
/* T-11 — procedural precondition contract (G-8)                            */
/* ------------------------------------------------------------------------- */

typedef struct {
  const fbs_goap_domain *d;
  fbs_goap_action veto;
  size_t state_size;
  unsigned calls;
  unsigned char log[64u * 1024u];
  size_t log_len;
  int record;
} proc_ctx;

static int proc_always(void *user, fbs_goap_action act, const fbs_goap_state *s) {
  proc_ctx *c = (proc_ctx *)user;
  ++c->calls;
  if (c->record && c->log_len + c->state_size + 2u <= sizeof c->log) {
    c->log[c->log_len++] = (unsigned char)(act & 0xffu);
    c->log[c->log_len++] = (unsigned char)((act >> 8) & 0xffu);
    memcpy(c->log + c->log_len, s, c->state_size);
    c->log_len += c->state_size;
  }
  return act == c->veto ? 0 : 1;
}

static void test_t11_proc_pre(void) {
  soldier s;
  state_buf sb;
  fbs_goap_state *start;
  fbs_goap_planner *p = NULL;
  fbs_goap_action plan[8], plan_null[8];
  fbs_goap_result res, res_null;
  fbs_goap_cond goal[2];
  fbs_goap_request req;
  proc_ctx *a = (proc_ctx *)malloc(sizeof(proc_ctx));
  proc_ctx *b = (proc_ctx *)malloc(sizeof(proc_ctx));

  CHECK(a != NULL && b != NULL);
  if (!a || !b) {
    free(a);
    free(b);
    return;
  }
  soldier_build(&s, 1, 1, 0);
  start = soldier_start(&s, &sb);
  CHECK(fbs_goap_planner_create(s.d, NULL, NULL, &p) == FBS_GOAP_OK);
  goal[0] = mk_cond(s.enemyalive, FBS_GOAP_EQ, 0);
  goal[1] = mk_cond(s.alive, FBS_GOAP_EQ, 1);

  /* (a) proc_pre == NULL means applicable, exactly like a callback that always
   * says yes — the opposite of the source's silent "never applicable" */
  memset(a, 0, sizeof *a);
  a->d = s.d;
  a->veto = FBS_GOAP_ACTION_NONE;
  a->state_size = fbs_goap_state_size(s.d);
  req = mk_request(start, goal, 2u, FBS_GOAP_H_ZERO);
  CHECK(fbs_goap_plan(p, &req, plan_null, 8u, &res_null) == FBS_GOAP_OK);
  req.proc_pre = proc_always;
  req.user = a;
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == res_null.outcome);
  CHECK(res.plan_len == res_null.plan_len);
  CHECK(res.plan_cost == res_null.plan_cost);
  CHECK(res.nodes_expanded == res_null.nodes_expanded);
  CHECK(memcmp(plan, plan_null, res.plan_len * sizeof plan[0]) == 0);
  CHECK(a->calls > 0u);

  /* (b) vetoing shoot makes the second goal unsolvable: detonatebomb kills the
   * planner's own agent, which the goal forbids */
  memset(a, 0, sizeof *a);
  a->d = s.d;
  a->veto = s.shoot;
  a->state_size = fbs_goap_state_size(s.d);
  req.user = a;
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_UNSOLVABLE);
  CHECK(res.plan_len == 0u);

  /* (c) the (action, state) sequence handed to proc_pre is identical across
   * two identical runs — the contract callers rely on for determinism */
  memset(a, 0, sizeof *a);
  memset(b, 0, sizeof *b);
  a->d = b->d = s.d;
  a->veto = b->veto = FBS_GOAP_ACTION_NONE;
  a->state_size = b->state_size = fbs_goap_state_size(s.d);
  a->record = b->record = 1;
  req.user = a;
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  req.user = b;
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(a->calls == b->calls);
  CHECK(a->log_len == b->log_len);
  CHECK(a->log_len > 0u);
  CHECK(memcmp(a->log, b->log, a->log_len) == 0);

  /* plan_validate honours proc_pre too */
  {
    size_t fi = 99u;
    int met = 0;
    memset(a, 0, sizeof *a);
    a->d = s.d;
    a->veto = s.shoot;
    a->state_size = fbs_goap_state_size(s.d);
    req.proc_pre = NULL;
    req.user = NULL;
    CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_FOUND);
    CHECK(fbs_goap_plan_validate(p, start, plan, res.plan_len, goal, 2u, proc_always, a, &fi,
                                 &met) == FBS_GOAP_OK);
    CHECK(fi == 3u); /* the shoot step, index 3, is vetoed */
    CHECK(met == 0);
    fi = 99u;
    CHECK(fbs_goap_plan_validate(p, start, plan, res.plan_len, goal, 2u, NULL, NULL, &fi, &met) ==
          FBS_GOAP_OK);
    CHECK(fi == res.plan_len);
    CHECK(met == 1);
  }

  free(a);
  free(b);
  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(s.d);
}

/* ------------------------------------------------------------------------- */
/* T-12 — state schema (atom_count, known bitmap, values)                    */
/* ------------------------------------------------------------------------- */

static void test_t12_state_schema(void) {
  soldier s;
  state_buf b1, b2;
  fbs_goap_state *x, *y;
  size_t size;
  unsigned i;

  soldier_build(&s, 1, 1, 0);
  size = fbs_goap_state_size(s.d);
  /* 4 (atom_count) + 4 * ceil(8/32) + 4 * 8 */
  CHECK(size == 4u + 4u * 1u + 4u * 8u);
  CHECK(size == 40u);

  x = state_new(s.d, &b1);
  y = state_new(s.d, &b2);
  CHECK(memcmp(x, y, size) == 0);
  CHECK(fbs_goap_state_equal(s.d, x, y) == 1);

  /* the atom_count guard word is the first field, little endian */
  {
    unsigned char raw[4];
    memcpy(raw, x, 4u);
    CHECK(raw[0] == 8u && raw[1] == 0u && raw[2] == 0u && raw[3] == 0u);
  }

  /* different set/unset histories that end logically equal are byte identical */
  state_put(s.d, x, s.enemyalive, 1);
  state_put(s.d, x, s.alive, 1);
  state_put(s.d, y, s.alive, 1);
  state_put(s.d, y, s.enemyvisible, 1);
  state_put(s.d, y, s.enemyalive, 0);
  CHECK(memcmp(x, y, size) != 0);
  CHECK(fbs_goap_state_equal(s.d, x, y) == 0);
  CHECK(fbs_goap_state_unset(s.d, y, s.enemyvisible) == FBS_GOAP_OK);
  state_put(s.d, y, s.enemyalive, 1);
  CHECK(memcmp(x, y, size) == 0); /* unknown slots forced back to zero */
  CHECK(fbs_goap_state_equal(s.d, x, y) == 1);

  /* every slot unknown after init; every slot known at its default after
   * init_defaults */
  {
    state_buf b3;
    fbs_goap_state *z = state_new(s.d, &b3);
    for (i = 0u; i < fbs_goap_atom_count(s.d); ++i) {
      int32_t v = 12345;
      CHECK(fbs_goap_state_known(s.d, z, (fbs_goap_atom)i) == 0);
      CHECK(fbs_goap_state_get(s.d, z, (fbs_goap_atom)i, &v) == FBS_GOAP_E_NOT_FOUND);
      CHECK(v == 12345); /* untouched on error */
    }
    z = state_new_defaults(s.d, &b3);
    for (i = 0u; i < fbs_goap_atom_count(s.d); ++i) {
      int32_t v = 0, lo = 0, hi = 0, def = 0;
      CHECK(fbs_goap_state_known(s.d, z, (fbs_goap_atom)i) == 1);
      CHECK(fbs_goap_state_get(s.d, z, (fbs_goap_atom)i, &v) == FBS_GOAP_OK);
      CHECK(fbs_goap_atom_range(s.d, (fbs_goap_atom)i, &lo, &hi, &def) == FBS_GOAP_OK);
      CHECK(v == def);
    }
    /* copy is byte exact */
    CHECK(fbs_goap_state_copy(s.d, x, z) == FBS_GOAP_OK);
    CHECK(memcmp(x, z, size) == 0);
  }

  /* a state of a different domain is rejected on atom_count */
  {
    fbs_goap_domain *e = make_domain();
    fbs_goap_atom only = atom_add(e, "only", 0, 1, 0);
    state_buf eb;
    fbs_goap_state *es;
    int32_t v = 0;
    CHECK(fbs_goap_domain_seal(e) == FBS_GOAP_OK);
    es = state_new(e, &eb);
    CHECK(fbs_goap_state_size(e) != size);
    CHECK(fbs_goap_state_set(s.d, es, s.alive, 1) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_state_get(s.d, es, s.alive, &v) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_state_known(s.d, es, s.alive) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_state_equal(s.d, x, es) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_state_copy(s.d, x, es) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_apply(s.d, es, s.scout) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_action_applicable(s.d, es, s.scout) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_state_set(e, es, only, 1) == FBS_GOAP_OK); /* right domain, fine */
    fbs_goap_domain_destroy(e);
  }

  /* an unsealed domain has no states at all */
  {
    fbs_goap_domain *u = make_domain();
    state_buf ub;
    fbs_goap_state *us = (fbs_goap_state *)0x1;
    (void)atom_add(u, "x", 0, 1, 0);
    CHECK(fbs_goap_state_size(u) == 0u);
    CHECK(fbs_goap_state_init(u, ub.w, sizeof ub.w, &us) == FBS_GOAP_E_STATE);
    CHECK(us == (fbs_goap_state *)0x1);
    CHECK(fbs_goap_state_init_defaults(u, ub.w, sizeof ub.w, &us) == FBS_GOAP_E_STATE);
    CHECK(us == (fbs_goap_state *)0x1);
    fbs_goap_domain_destroy(u);
  }

  fbs_goap_domain_destroy(s.d);
}

/* ------------------------------------------------------------------------- */
/* T-13 — goal already satisfied is its own signal (G-4)                     */
/* ------------------------------------------------------------------------- */

static void test_t13_already_satisfied(void) {
  soldier s;
  state_buf sb;
  fbs_goap_state *start;
  fbs_goap_planner *p = NULL;
  fbs_goap_action plan[8];
  fbs_goap_result res;
  fbs_goap_cond goal[1];
  fbs_goap_request req;

  soldier_build(&s, 1, 1, 0);
  start = soldier_start(&s, &sb);
  CHECK(fbs_goap_planner_create(s.d, NULL, NULL, &p) == FBS_GOAP_OK);

  goal[0] = mk_cond(s.alive, FBS_GOAP_EQ, 1); /* true in the start state */
  req = mk_request(start, goal, 1u, FBS_GOAP_H_ZERO);
  memset(plan, 0xA5, sizeof plan);
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_ALREADY_SATISFIED);
  CHECK(res.plan_len == 0u);
  CHECK(res.plan_cost == 0);
  CHECK(res.nodes_expanded == 0u);
  CHECK(res.nodes_generated == 0u);
  CHECK(res.peak_open == 0u);
  CHECK(untouched(plan, sizeof plan, 0xA5));

  /* even with a zero plan buffer, and with the other heuristic */
  req.heuristic = FBS_GOAP_H_MAX_UNSAT;
  CHECK(fbs_goap_plan(p, &req, NULL, 0u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_ALREADY_SATISFIED);
  CHECK(res.nodes_expanded == 0u);

  /* an unsatisfied goal in the same shape is not ALREADY_SATISFIED */
  goal[0] = mk_cond(s.alive, FBS_GOAP_EQ, 0);
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_FOUND);
  CHECK(res.plan_len == 3u);

  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(s.d);
}

/* ------------------------------------------------------------------------- */
/* T-15 — truncation, capacity, allocator failure, sealing                   */
/* ------------------------------------------------------------------------- */

static void test_t15_truncation_and_capacity(void) {
  soldier s;
  state_buf sb;
  fbs_goap_state *start;
  fbs_goap_planner *p = NULL;
  fbs_goap_action plan[8];
  fbs_goap_result res;
  fbs_goap_cond goal[1];
  fbs_goap_request req;
  size_t n = 0;

  soldier_build(&s, 1, 1, 0);
  start = soldier_start(&s, &sb);
  CHECK(fbs_goap_planner_create(s.d, NULL, NULL, &p) == FBS_GOAP_OK);
  goal[0] = mk_cond(s.enemyalive, FBS_GOAP_EQ, 0);
  req = mk_request(start, goal, 1u, FBS_GOAP_H_ZERO);

  /* plan_cap too small: PLAN_TRUNCATED, plan_len = the REQUIRED length, and
   * the caller's buffer is left alone (GPGOAP hangs on exactly this case) */
  {
    size_t cap;
    for (cap = 0u; cap < 3u; ++cap) {
      memset(plan, 0xA5, sizeof plan);
      CHECK(fbs_goap_plan(p, &req, cap ? plan : NULL, cap, &res) == FBS_GOAP_OK);
      CHECK(res.outcome == FBS_GOAP_PLAN_TRUNCATED);
      CHECK(res.plan_len == 3u);
      CHECK(res.plan_cost == 3);
      CHECK(untouched(plan, sizeof plan, 0xA5));
    }
    memset(plan, 0xA5, sizeof plan);
    CHECK(fbs_goap_plan(p, &req, plan, 3u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_FOUND);
    CHECK(res.plan_len == 3u);
    CHECK(untouched(plan + 3, 5u * sizeof plan[0], 0xA5)); /* nothing beyond the plan */
  }

  /* listing truncation reports the required count */
  {
    fbs_goap_cond conds[4];
    fbs_goap_effect effs[4];
    CHECK(fbs_goap_action_conditions(s.d, s.detonate, conds, 1u, &n) == FBS_GOAP_E_TRUNCATED);
    CHECK(n == 2u);
    CHECK(fbs_goap_action_conditions(s.d, s.detonate, NULL, 0u, &n) == FBS_GOAP_E_TRUNCATED);
    CHECK(n == 2u);
    CHECK(fbs_goap_action_conditions(s.d, s.detonate, conds, 4u, &n) == FBS_GOAP_OK);
    CHECK(n == 2u);
    CHECK(fbs_goap_action_effects(s.d, s.detonate, effs, 1u, &n) == FBS_GOAP_E_TRUNCATED);
    CHECK(n == 2u);
    CHECK(fbs_goap_action_effects(s.d, s.detonate, effs, 4u, &n) == FBS_GOAP_OK);
    CHECK(n == 2u);
    CHECK(fbs_goap_action_effects(s.d, s.flee, effs, 0u, &n) == FBS_GOAP_E_TRUNCATED);
    CHECK(n == 1u);
  }

  /* serialization truncation */
  {
    unsigned char small[8];
    size_t len = 0;
    size_t need = fbs_goap_domain_serialized_size(s.d);
    CHECK(need > sizeof small);
    memset(small, 0xA5, sizeof small);
    CHECK(fbs_goap_domain_serialize(s.d, small, sizeof small, &len) == FBS_GOAP_E_TRUNCATED);
    CHECK(len == need);
    CHECK(untouched(small, sizeof small, 0xA5));
  }

  /* registration after seal is E_SEALED, and clear unseals */
  {
    fbs_goap_atom a = FBS_GOAP_ATOM_NONE;
    fbs_goap_action act = FBS_GOAP_ACTION_NONE;
    CHECK(fbs_goap_domain_is_sealed(s.d) == 1);
    CHECK(fbs_goap_atom_add(s.d, "late", 4u, 0, 1, 0, &a) == FBS_GOAP_E_SEALED);
    CHECK(a == FBS_GOAP_ATOM_NONE);
    CHECK(fbs_goap_action_add(s.d, "late", 4u, 1, &act) == FBS_GOAP_E_SEALED);
    CHECK(act == FBS_GOAP_ACTION_NONE);
    CHECK(fbs_goap_action_pre(s.d, s.scout, s.alive, FBS_GOAP_EQ, 1) == FBS_GOAP_E_SEALED);
    CHECK(fbs_goap_action_effect(s.d, s.scout, s.alive, FBS_GOAP_SET, 1) == FBS_GOAP_E_SEALED);
    CHECK(fbs_goap_domain_seal(s.d) == FBS_GOAP_OK); /* idempotent */
  }

  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(s.d);

  /* capacity exhaustion on every configured limit */
  {
    fbs_goap_config cfg = fbs_goap_config_default();
    fbs_goap_domain *d = NULL;
    fbs_goap_atom a = FBS_GOAP_ATOM_NONE, a0;
    fbs_goap_action act = FBS_GOAP_ACTION_NONE, act0;

    cfg.max_atoms = 2u;
    cfg.max_actions = 2u;
    cfg.max_conditions = 1u;
    cfg.max_effects = 1u;
    cfg.max_key_bytes = 16u;
    CHECK(fbs_goap_domain_create(&cfg, NULL, &d) == FBS_GOAP_OK);
    a0 = atom_add(d, "aa", 0, 1, 0);
    (void)atom_add(d, "bb", 0, 1, 0);
    CHECK(fbs_goap_atom_add(d, "cc", 2u, 0, 1, 0, &a) == FBS_GOAP_E_FULL);
    CHECK(a == FBS_GOAP_ATOM_NONE);
    act0 = action_add(d, "xx", 1);
    (void)action_add(d, "yy", 1);
    CHECK(fbs_goap_action_add(d, "zz", 2u, 1, &act) == FBS_GOAP_E_FULL);
    CHECK(act == FBS_GOAP_ACTION_NONE);
    CHECK(fbs_goap_action_pre(d, act0, a0, FBS_GOAP_EQ, 1) == FBS_GOAP_OK);
    CHECK(fbs_goap_action_pre(d, act0, a0, FBS_GOAP_EQ, 0) == FBS_GOAP_E_FULL);
    CHECK(fbs_goap_action_effect(d, act0, a0, FBS_GOAP_SET, 1) == FBS_GOAP_OK);
    CHECK(fbs_goap_action_effect(d, act0, a0, FBS_GOAP_SET, 0) == FBS_GOAP_E_EXISTS);
    CHECK(fbs_goap_action_effect(d, act0, (fbs_goap_atom)1u, FBS_GOAP_SET, 1) == FBS_GOAP_E_FULL);
    fbs_goap_domain_destroy(d);

    /* key bytes */
    cfg = fbs_goap_config_default();
    cfg.max_key_bytes = 8u;
    CHECK(fbs_goap_domain_create(&cfg, NULL, &d) == FBS_GOAP_OK);
    (void)atom_add(d, "abcd", 0, 1, 0);
    CHECK(fbs_goap_atom_add(d, "efghi", 5u, 0, 1, 0, &a) == FBS_GOAP_E_FULL);
    CHECK(fbs_goap_action_add(d, "efghi", 5u, 1, &act) == FBS_GOAP_E_FULL);
    CHECK(fbs_goap_atom_add(d, "efgh", 4u, 0, 1, 0, &a) == FBS_GOAP_OK);
    fbs_goap_domain_destroy(d);

    /* duplicate keys, and the two namespaces are separate */
    d = make_domain();
    (void)atom_add(d, "dup", 0, 1, 0);
    CHECK(fbs_goap_atom_add(d, "dup", 3u, 0, 1, 0, &a) == FBS_GOAP_E_EXISTS);
    CHECK(fbs_goap_action_add(d, "dup", 3u, 1, &act) == FBS_GOAP_OK); /* other namespace */
    CHECK(fbs_goap_action_add(d, "dup", 3u, 1, &act) == FBS_GOAP_E_EXISTS);
    /* duplicate identical precondition rows are rejected, distinct ones are not */
    CHECK(fbs_goap_action_pre(d, act, 0u, FBS_GOAP_EQ, 1) == FBS_GOAP_OK);
    CHECK(fbs_goap_action_pre(d, act, 0u, FBS_GOAP_EQ, 1) == FBS_GOAP_E_EXISTS);
    CHECK(fbs_goap_action_pre(d, act, 0u, FBS_GOAP_NE, 1) == FBS_GOAP_OK);
    CHECK(fbs_goap_action_pre(d, act, 0u, FBS_GOAP_EQ, 0) == FBS_GOAP_OK);
    fbs_goap_domain_destroy(d);
  }

  /* allocator failure on every allocating entry point */
  {
    counting_alloc ca;
    fbs_goap_allocator alloc;
    fbs_goap_domain *d = (fbs_goap_domain *)0x1;
    fbs_goap_planner *pl = (fbs_goap_planner *)0x1;
    unsigned char *blob;
    size_t len = 0;

    ca.allocs = 0;
    ca.frees = 0;
    ca.bytes = 0u;
    ca.budget = 0;
    alloc.alloc = ca_alloc;
    alloc.free = ca_free;
    alloc.user = &ca;
    CHECK(fbs_goap_domain_create(NULL, &alloc, &d) == FBS_GOAP_E_MEMORY);
    CHECK(d == (fbs_goap_domain *)0x1);

    ca.budget = -1;
    CHECK(fbs_goap_domain_create(NULL, &alloc, &d) == FBS_GOAP_OK);
    CHECK(ca.allocs == 1); /* exactly one allocation per object */
    CHECK(fbs_goap_domain_memory(d) == ca.bytes);
    (void)atom_add(d, "a", 0, 1, 0);
    (void)action_add(d, "act", 1);
    CHECK(fbs_goap_domain_seal(d) == FBS_GOAP_OK);
    CHECK(ca.allocs == 1); /* nothing is allocated after create */

    ca.budget = 0;
    CHECK(fbs_goap_planner_create(d, NULL, &alloc, &pl) == FBS_GOAP_E_MEMORY);
    CHECK(pl == (fbs_goap_planner *)0x1);
    ca.budget = -1;
    CHECK(fbs_goap_planner_create(d, NULL, &alloc, &pl) == FBS_GOAP_OK);
    CHECK(ca.allocs == 2);
    CHECK(fbs_goap_planner_memory(pl) > 0u);

    blob = serialize_alloc(d, &len);
    ca.budget = 0;
    {
      fbs_goap_domain *g = (fbs_goap_domain *)0x1;
      CHECK(fbs_goap_domain_deserialize(blob, len, NULL, &alloc, &g) == FBS_GOAP_E_MEMORY);
      CHECK(g == (fbs_goap_domain *)0x1);
      ca.budget = -1;
      CHECK(fbs_goap_domain_deserialize(blob, len, NULL, &alloc, &g) == FBS_GOAP_OK);
      fbs_goap_domain_destroy(g);
    }
    free(blob);

    fbs_goap_planner_destroy(pl);
    fbs_goap_domain_destroy(d);
    CHECK(ca.allocs == ca.frees);

    /* a half-populated allocator struct is rejected outright */
    alloc.alloc = NULL;
    d = (fbs_goap_domain *)0x1;
    CHECK(fbs_goap_domain_create(NULL, &alloc, &d) == FBS_GOAP_E_INVALID);
    CHECK(d == (fbs_goap_domain *)0x1);
    alloc.alloc = ca_alloc;
    alloc.free = NULL;
    CHECK(fbs_goap_domain_create(NULL, &alloc, &d) == FBS_GOAP_E_INVALID);
  }
}

/* ------------------------------------------------------------------------- */
/* T-16 — serialization round trip and schema rejection                      */
/* ------------------------------------------------------------------------- */

static void expect_schema_reject(const unsigned char *blob, size_t len, const char *what) {
  fbs_goap_domain *d = (fbs_goap_domain *)0x1;
  fbs_goap_status st = fbs_goap_domain_deserialize(blob, len, NULL, NULL, &d);
  ++g_checks;
  if (st != FBS_GOAP_E_SCHEMA || d != (fbs_goap_domain *)0x1) {
    ++g_fails;
    printf("FAIL schema rejection (%s): status %s, out %s\n", what, fbs_goap_status_name(st),
           d == (fbs_goap_domain *)0x1 ? "untouched" : "WRITTEN");
    if (st == FBS_GOAP_OK) fbs_goap_domain_destroy(d);
  }
}

static void test_t16_serialization(void) {
  soldier s;
  unsigned char *blob;
  unsigned char *copy;
  size_t len = 0, len2 = 0;
  fbs_goap_domain *g = NULL;

  soldier_build(&s, 1, 1, 0);
  blob = serialize_alloc(s.d, &len);
  /* 28 header + 8*20 atoms + 7*20 actions + 7*8 effect slices + 9*8 conds
   * + 8*8 effects + 85 atom key bytes + 41 action key bytes */
  CHECK(len == 28u + 160u + 140u + 56u + 72u + 64u + 85u + 41u);
  CHECK(len == 646u);
  CHECK(fbs_goap_domain_deserialize(blob, len, NULL, NULL, &g) == FBS_GOAP_OK);
  CHECK(fbs_goap_domain_is_sealed(g) == 1);
  CHECK(fbs_goap_atom_count(g) == fbs_goap_atom_count(s.d));
  CHECK(fbs_goap_action_count(g) == fbs_goap_action_count(s.d));

  /* fixed point at the byte level */
  copy = serialize_alloc(g, &len2);
  CHECK(len2 == len);
  CHECK(memcmp(copy, blob, len) == 0);

  /* keys, ranges, costs and rows survive */
  {
    fbs_goap_atom a = FBS_GOAP_ATOM_NONE;
    fbs_goap_action act = FBS_GOAP_ACTION_NONE;
    const char *key = NULL;
    size_t klen = 0;
    int32_t lo = 0, hi = 0, def = 0;
    fbs_goap_cost cost = -1;
    fbs_goap_cond rows[4];
    size_t n = 0;
    CHECK(fbs_goap_atom_find(g, "enemyalive", 10u, &a) == FBS_GOAP_OK);
    CHECK(a == s.enemyalive);
    CHECK(fbs_goap_atom_key(g, a, &key, &klen) == FBS_GOAP_OK);
    CHECK(klen == 10u && memcmp(key, "enemyalive", 10u) == 0);
    CHECK(fbs_goap_atom_range(g, a, &lo, &hi, &def) == FBS_GOAP_OK);
    CHECK(lo == 0 && hi == 1 && def == 0);
    CHECK(fbs_goap_action_find(g, "detonatebomb", 12u, &act) == FBS_GOAP_OK);
    CHECK(act == s.detonate);
    CHECK(fbs_goap_action_cost(g, act, &cost) == FBS_GOAP_OK);
    CHECK(cost == 1);
    CHECK(fbs_goap_action_conditions(g, act, rows, 4u, &n) == FBS_GOAP_OK);
    CHECK(n == 2u);
    CHECK(rows[0].atom == s.armedwithbomb && rows[0].cmp == (uint8_t)FBS_GOAP_EQ);
    CHECK(rows[1].atom == s.nearenemy);
    CHECK(fbs_goap_action_find(g, "nosuch", 6u, &act) == FBS_GOAP_E_NOT_FOUND);
    CHECK(fbs_goap_atom_find(g, "nosuch", 6u, &a) == FBS_GOAP_E_NOT_FOUND);
  }

  /* the round-tripped domain produces T-1's plan exactly */
  {
    state_buf sb;
    soldier gs = s;
    fbs_goap_state *start;
    fbs_goap_planner *p = NULL;
    fbs_goap_action plan[8];
    fbs_goap_result res;
    fbs_goap_cond goal[1];
    fbs_goap_request req;
    char keys[128];
    gs.d = g;
    start = soldier_start(&gs, &sb);
    CHECK(fbs_goap_planner_create(g, NULL, NULL, &p) == FBS_GOAP_OK);
    goal[0] = mk_cond(gs.enemyalive, FBS_GOAP_EQ, 0);
    req = mk_request(start, goal, 1u, FBS_GOAP_H_MAX_UNSAT);
    CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
    CHECK(res.outcome == FBS_GOAP_FOUND);
    plan_to_keys(g, plan, res.plan_len, keys, sizeof keys);
    CHECK(strcmp(keys, "scout approach detonatebomb") == 0);
    CHECK(res.plan_cost == 3);
    fbs_goap_planner_destroy(p);
  }
  fbs_goap_domain_destroy(g);

  /* corruption of every guarded field is E_SCHEMA, never a crash */
  {
    unsigned char *bad = (unsigned char *)malloc(len);
    CHECK(bad != NULL);
    if (bad) {
      size_t i;
      memcpy(bad, blob, len);
      bad[0] = 'X';
      expect_schema_reject(bad, len, "magic");
      memcpy(bad, blob, len);
      bad[4] = 9u;
      expect_schema_reject(bad, len, "version");
      memcpy(bad, blob, len);
      bad[6] = 1u;
      expect_schema_reject(bad, len, "flags");
      memcpy(bad, blob, len);
      bad[24] = 1u;
      expect_schema_reject(bad, len, "reserved");
      memcpy(bad, blob, len);
      expect_schema_reject(bad, len - 1u, "short length");
      expect_schema_reject(bad, 4u, "header truncated");
      memcpy(bad, blob, len);
      bad[8] = 9u; /* atom_count */
      expect_schema_reject(bad, len, "atom count");
      memcpy(bad, blob, len);
      bad[12] = 99u; /* cond_count */
      expect_schema_reject(bad, len, "cond count");
      memcpy(bad, blob, len);
      bad[28] = 1u; /* first atom key_off must be 0 */
      expect_schema_reject(bad, len, "atom key offset");
      memcpy(bad, blob, len);
      bad[28 + 4] = 0u; /* first atom key_len 0 */
      expect_schema_reject(bad, len, "atom key length");
      memcpy(bad, blob, len);
      bad[28 + 8] = 5u; /* min > max on the first atom */
      expect_schema_reject(bad, len, "atom min > max");
      memcpy(bad, blob, len);
      /* first action record: cost negative */
      bad[28 + 160 + 11] = 0x80u;
      expect_schema_reject(bad, len, "negative cost");
      memcpy(bad, blob, len);
      /* first action record: cond_off must be 0 */
      bad[28 + 160 + 12] = 3u;
      expect_schema_reject(bad, len, "cond slice offset");
      memcpy(bad, blob, len);
      /* first action record: cond_count beyond the array */
      bad[28 + 160 + 16] = 99u;
      expect_schema_reject(bad, len, "cond slice length");
      memcpy(bad, blob, len);
      /* first effect slice offset must be 0 */
      bad[28 + 160 + 140] = 2u;
      expect_schema_reject(bad, len, "effect slice offset");
      memcpy(bad, blob, len);
      /* condition row: atom id beyond the table */
      bad[28 + 160 + 140 + 56] = 99u;
      expect_schema_reject(bad, len, "row atom id");
      memcpy(bad, blob, len);
      /* condition row: bad comparator */
      bad[28 + 160 + 140 + 56 + 2] = 9u;
      expect_schema_reject(bad, len, "row comparator");
      memcpy(bad, blob, len);
      /* condition row: non-zero padding */
      bad[28 + 160 + 140 + 56 + 3] = 1u;
      expect_schema_reject(bad, len, "row padding");
      memcpy(bad, blob, len);
      /* effect row: bad op (first effect row follows all 9 condition rows) */
      bad[28 + 160 + 140 + 56 + 72 + 2] = 7u;
      expect_schema_reject(bad, len, "effect op");
      memcpy(bad, blob, len);
      /* duplicate atom key: the key blob is the last 126 bytes and starts with
       * "enemyvisible" then "armedwithgun", both 12 bytes, so copying the
       * first over the second makes two atoms share a key */
      i = len - 126u;
      memcpy(bad + i + 12u, bad + i, 12u);
      expect_schema_reject(bad, len, "duplicate atom key");
      free(bad);
    }
  }

  /* an explicit config that cannot hold the blob is E_FULL, not E_SCHEMA */
  {
    fbs_goap_config cfg = fbs_goap_config_default();
    fbs_goap_domain *h = (fbs_goap_domain *)0x1;
    cfg.max_atoms = 2u;
    CHECK(fbs_goap_domain_deserialize(blob, len, &cfg, NULL, &h) == FBS_GOAP_E_FULL);
    CHECK(h == (fbs_goap_domain *)0x1);
    cfg = fbs_goap_config_default();
    cfg.max_actions = 2u;
    CHECK(fbs_goap_domain_deserialize(blob, len, &cfg, NULL, &h) == FBS_GOAP_E_FULL);
    cfg = fbs_goap_config_default();
    cfg.max_conditions = 2u;
    CHECK(fbs_goap_domain_deserialize(blob, len, &cfg, NULL, &h) == FBS_GOAP_E_FULL);
    cfg = fbs_goap_config_default();
    cfg.max_effects = 2u;
    CHECK(fbs_goap_domain_deserialize(blob, len, &cfg, NULL, &h) == FBS_GOAP_E_FULL);
    cfg = fbs_goap_config_default();
    cfg.max_key_bytes = 4u;
    CHECK(fbs_goap_domain_deserialize(blob, len, &cfg, NULL, &h) == FBS_GOAP_E_FULL);
    cfg = fbs_goap_config_default();
    cfg.max_atoms = 0u;
    CHECK(fbs_goap_domain_deserialize(blob, len, &cfg, NULL, &h) == FBS_GOAP_E_INVALID);
    CHECK(h == (fbs_goap_domain *)0x1);
    cfg = fbs_goap_config_default();
    cfg.max_atoms = 4096u;
    cfg.max_actions = 4096u;
    CHECK(fbs_goap_domain_deserialize(blob, len, &cfg, NULL, &h) == FBS_GOAP_OK);
    CHECK(fbs_goap_atom_count(h) == 8u);
    fbs_goap_domain_destroy(h);
  }

  /* an empty sealed domain round-trips too */
  {
    fbs_goap_domain *e = make_domain();
    fbs_goap_domain *f = NULL;
    unsigned char *eb;
    size_t elen = 0;
    CHECK(fbs_goap_domain_seal(e) == FBS_GOAP_OK);
    eb = serialize_alloc(e, &elen);
    CHECK(elen == 28u);
    CHECK(fbs_goap_domain_deserialize(eb, elen, NULL, NULL, &f) == FBS_GOAP_OK);
    CHECK(fbs_goap_atom_count(f) == 0u);
    CHECK(fbs_goap_action_count(f) == 0u);
    CHECK(fbs_goap_state_size(f) == 4u);
    free(eb);
    fbs_goap_domain_destroy(f);
    fbs_goap_domain_destroy(e);
  }

  /* 4000 random byte flips: every one is either accepted (and then a usable
   * sealed domain) or refused with a defined status. Never a crash, never a
   * leak — this loop is the reason the sanitizer builds are mandatory. */
  {
    unsigned char *fuzz = (unsigned char *)malloc(len);
    int accepted = 0, refused = 0, k;
    CHECK(fuzz != NULL);
    rng_seed(0x0A11CE01u);
    for (k = 0; k < 4000 && fuzz; ++k) {
      fbs_goap_domain *h = NULL;
      size_t at = (size_t)rng_below((unsigned)len);
      fbs_goap_status st;
      memcpy(fuzz, blob, len);
      fuzz[at] ^= (unsigned char)(1u << rng_below(8u));
      st = fbs_goap_domain_deserialize(fuzz, len, NULL, NULL, &h);
      if (st == FBS_GOAP_OK) {
        ++accepted;
        CHECK(fbs_goap_domain_is_sealed(h) == 1);
        /* whatever it decoded to, it is a well formed domain */
        CHECK(fbs_goap_domain_serialized_size(h) > 0u);
        CHECK(fbs_goap_state_size(h) == 4u + 4u * ((fbs_goap_atom_count(h) + 31u) / 32u) +
                                            4u * fbs_goap_atom_count(h));
        fbs_goap_domain_destroy(h);
      } else {
        ++refused;
        if (st != FBS_GOAP_E_SCHEMA && st != FBS_GOAP_E_FULL && st != FBS_GOAP_E_MEMORY) {
          ++g_fails;
          printf("FAIL fuzz: unexpected status %s\n", fbs_goap_status_name(st));
        }
        ++g_checks;
      }
    }
    CHECK(accepted > 0); /* the corpus is not all rejections */
    CHECK(refused > 0);
    free(fuzz);
  }

  /* an unsealed domain cannot be serialized */
  {
    fbs_goap_domain *u = make_domain();
    unsigned char buf[64];
    size_t out = 0;
    (void)atom_add(u, "x", 0, 1, 0);
    CHECK(fbs_goap_domain_serialized_size(u) == 0u);
    CHECK(fbs_goap_domain_serialize(u, buf, sizeof buf, &out) == FBS_GOAP_E_STATE);
    fbs_goap_domain_destroy(u);
  }

  free(copy);
  free(blob);
  fbs_goap_domain_destroy(s.d);
}

/* ------------------------------------------------------------------------- */
/* domain_clear, and a cleared domain is unsealed and empty                  */
/* ------------------------------------------------------------------------- */

static void test_domain_clear(void) {
  soldier s;
  unsigned char *b1, *b2;
  size_t l1 = 0, l2 = 0;
  fbs_goap_planner *p = NULL;
  state_buf sb;
  fbs_goap_state *start;
  fbs_goap_cond goal[1];
  fbs_goap_request req;
  fbs_goap_result res;
  fbs_goap_action plan[8];

  soldier_build(&s, 1, 1, 0);
  b1 = serialize_alloc(s.d, &l1);
  CHECK(fbs_goap_atom_count(s.d) == 8u);

  /* Clearing a domain a planner still points at is documented as the caller's
   * mistake; it must still be reported rather than read through. */
  start = soldier_start(&s, &sb);
  goal[0] = mk_cond(s.enemyalive, FBS_GOAP_EQ, 0);
  req = mk_request(start, goal, 1u, FBS_GOAP_H_ZERO);
  CHECK(fbs_goap_planner_create(s.d, NULL, NULL, &p) == FBS_GOAP_OK);
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  fbs_goap_domain_clear(s.d);
  memset(&res, 0xA5, sizeof res);
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_E_STATE); /* unsealed now */
  CHECK(untouched(&res, sizeof res, 0xA5));
  fbs_goap_planner_destroy(p);

  CHECK(fbs_goap_domain_is_sealed(s.d) == 0);
  CHECK(fbs_goap_atom_count(s.d) == 0u);
  CHECK(fbs_goap_action_count(s.d) == 0u);
  CHECK(fbs_goap_state_size(s.d) == 0u);
  {
    fbs_goap_atom a = FBS_GOAP_ATOM_NONE;
    CHECK(fbs_goap_atom_find(s.d, "alive", 5u, &a) == FBS_GOAP_E_NOT_FOUND);
  }

  /* rebuilding the identical domain reproduces the identical bytes */
  {
    soldier again;
    soldier_build(&again, 1, 1, 0);
    b2 = serialize_alloc(again.d, &l2);
    CHECK(l1 == l2 && memcmp(b1, b2, l1) == 0);
    free(b2);
    fbs_goap_domain_destroy(again.d);
  }
  free(b1);
  fbs_goap_domain_destroy(s.d);
}

/* ------------------------------------------------------------------------- */
/* A wide domain: plan_validate borrows the planner's scratch, never the heap */
/* ------------------------------------------------------------------------- */

static void test_wide_domain(void) {
  fbs_goap_config cfg = fbs_goap_config_default();
  fbs_goap_planner_config pcfg = fbs_goap_planner_config_default();
  fbs_goap_domain *d = NULL;
  fbs_goap_planner *p = NULL;
  fbs_goap_state *st = NULL;
  void *buf;
  unsigned i;
  const unsigned n = 600u; /* past the 512-atom inline buffer in plan_validate */
  fbs_goap_action last = FBS_GOAP_ACTION_NONE;
  fbs_goap_cond goal[1];
  fbs_goap_action plan[4];
  fbs_goap_result res;
  fbs_goap_request req;
  size_t first_invalid = 99u;
  int met = 0;

  cfg.max_atoms = n;
  cfg.max_actions = 2u;
  cfg.max_conditions = 2u;
  cfg.max_effects = 2u;
  CHECK(fbs_goap_domain_create(&cfg, NULL, &d) == FBS_GOAP_OK);
  for (i = 0u; i < n; ++i) {
    char key[24];
    sprintf(key, "w%u", i);
    (void)atom_add(d, key, 0, 1, 0);
  }
  last = action_add(d, "finish", 1);
  CHECK(fbs_goap_action_effect(d, last, (fbs_goap_atom)(n - 1u), FBS_GOAP_SET, 1) == FBS_GOAP_OK);
  CHECK(fbs_goap_domain_seal(d) == FBS_GOAP_OK);

  CHECK(fbs_goap_state_size(d) == 4u + 4u * ((n + 31u) / 32u) + 4u * n);
  buf = malloc(fbs_goap_state_size(d));
  CHECK(buf != NULL);
  if (!buf) {
    fbs_goap_domain_destroy(d);
    return;
  }
  CHECK(fbs_goap_state_init_defaults(d, buf, fbs_goap_state_size(d), &st) == FBS_GOAP_OK);

  pcfg.max_nodes = 16u;
  CHECK(fbs_goap_planner_create(d, &pcfg, NULL, &p) == FBS_GOAP_OK);
  goal[0] = mk_cond((fbs_goap_atom)(n - 1u), FBS_GOAP_EQ, 1);
  req = mk_request(st, goal, 1u, FBS_GOAP_H_MAX_UNSAT);
  CHECK(fbs_goap_plan(p, &req, plan, 4u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_FOUND);
  CHECK(res.plan_len == 1u);
  CHECK(plan[0] == last);
  /* the validate path that has to fall back to the heap for its working copy */
  CHECK(fbs_goap_plan_validate(p, st, plan, res.plan_len, goal, 1u, NULL, NULL, &first_invalid,
                               &met) == FBS_GOAP_OK);
  CHECK(first_invalid == 1u);
  CHECK(met == 1);

  free(buf);
  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(d);
}

/* ------------------------------------------------------------------------- */
/* NULL, bad enum and bad id on every entry point                            */
/* ------------------------------------------------------------------------- */

static void test_invalid_arguments(void) {
  fbs_goap_domain *d = make_domain();
  fbs_goap_atom wood = atom_add(d, "wood", 0, 10, 0);
  fbs_goap_action chop = action_add(d, "chop", 1);
  fbs_goap_atom a = FBS_GOAP_ATOM_NONE;
  fbs_goap_action act = FBS_GOAP_ACTION_NONE;
  fbs_goap_planner *p = NULL;
  fbs_goap_config cfg;
  fbs_goap_planner_config pcfg;
  const char *key = NULL;
  size_t klen = 0, n = 0;
  int32_t lo = 0, hi = 0, def = 0, v = 0;
  fbs_goap_cost cost = 0;
  fbs_goap_cond conds[4];
  fbs_goap_effect effs[4];
  state_buf sb;
  fbs_goap_state *st;
  unsigned char raw[128];
  unsigned char *misaligned;

  CHECK(fbs_goap_action_effect(d, chop, wood, FBS_GOAP_ADD, 1) == FBS_GOAP_OK);

  /* create */
  CHECK(fbs_goap_domain_create(NULL, NULL, NULL) == FBS_GOAP_E_INVALID);
  {
    fbs_goap_domain *tmp = (fbs_goap_domain *)0x1;
    cfg = fbs_goap_config_default();
    cfg.max_atoms = 0u;
    CHECK(fbs_goap_domain_create(&cfg, NULL, &tmp) == FBS_GOAP_E_INVALID);
    cfg = fbs_goap_config_default();
    cfg.max_atoms = 4097u;
    CHECK(fbs_goap_domain_create(&cfg, NULL, &tmp) == FBS_GOAP_E_INVALID);
    cfg = fbs_goap_config_default();
    cfg.max_actions = 0u;
    CHECK(fbs_goap_domain_create(&cfg, NULL, &tmp) == FBS_GOAP_E_INVALID);
    cfg = fbs_goap_config_default();
    cfg.max_actions = 4097u;
    CHECK(fbs_goap_domain_create(&cfg, NULL, &tmp) == FBS_GOAP_E_INVALID);
    cfg = fbs_goap_config_default();
    cfg.max_conditions = (1u << 20) + 1u;
    CHECK(fbs_goap_domain_create(&cfg, NULL, &tmp) == FBS_GOAP_E_INVALID);
    cfg = fbs_goap_config_default();
    cfg.max_effects = (1u << 20) + 1u;
    CHECK(fbs_goap_domain_create(&cfg, NULL, &tmp) == FBS_GOAP_E_INVALID);
    cfg = fbs_goap_config_default();
    cfg.max_key_bytes = 0u;
    CHECK(fbs_goap_domain_create(&cfg, NULL, &tmp) == FBS_GOAP_E_INVALID);
    cfg = fbs_goap_config_default();
    cfg.max_key_bytes = (1u << 26) + 1u;
    CHECK(fbs_goap_domain_create(&cfg, NULL, &tmp) == FBS_GOAP_E_INVALID);
    CHECK(tmp == (fbs_goap_domain *)0x1);
  }

  /* accessors on NULL */
  CHECK(fbs_goap_atom_count(NULL) == 0u);
  CHECK(fbs_goap_action_count(NULL) == 0u);
  CHECK(fbs_goap_domain_memory(NULL) == 0u);
  CHECK(fbs_goap_planner_memory(NULL) == 0u);
  CHECK(fbs_goap_domain_is_sealed(NULL) == 0);
  CHECK(fbs_goap_state_size(NULL) == 0u);
  CHECK(fbs_goap_domain_serialized_size(NULL) == 0u);
  CHECK(fbs_goap_domain_seal(NULL) == FBS_GOAP_E_INVALID);
  fbs_goap_domain_destroy(NULL);
  fbs_goap_domain_clear(NULL);
  fbs_goap_planner_destroy(NULL);

  /* atoms */
  CHECK(fbs_goap_atom_add(NULL, "x", 1u, 0, 1, 0, &a) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_add(d, NULL, 1u, 0, 1, 0, &a) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_add(d, "x", 1u, 0, 1, 0, NULL) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_add(d, "x", 0u, 0, 1, 0, &a) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_add(d, "x", 256u, 0, 1, 0, &a) == FBS_GOAP_E_INVALID);
  CHECK(a == FBS_GOAP_ATOM_NONE);
  CHECK(fbs_goap_atom_find(NULL, "wood", 4u, &a) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_find(d, NULL, 4u, &a) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_find(d, "wood", 4u, NULL) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_find(d, "wood", 0u, &a) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_key(NULL, wood, &key, &klen) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_key(d, wood, NULL, &klen) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_key(d, wood, &key, NULL) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_key(d, (fbs_goap_atom)77u, &key, &klen) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_key(d, FBS_GOAP_ATOM_NONE, &key, &klen) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_range(NULL, wood, &lo, &hi, &def) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_range(d, wood, NULL, &hi, &def) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_range(d, wood, &lo, NULL, &def) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_range(d, wood, &lo, &hi, NULL) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_atom_range(d, (fbs_goap_atom)77u, &lo, &hi, &def) == FBS_GOAP_E_INVALID);

  /* actions and rows */
  CHECK(fbs_goap_action_add(NULL, "x", 1u, 1, &act) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_add(d, NULL, 1u, 1, &act) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_add(d, "x", 1u, 1, NULL) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_add(d, "x", 0u, 1, &act) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_add(d, "x", 256u, 1, &act) == FBS_GOAP_E_INVALID);
  CHECK(act == FBS_GOAP_ACTION_NONE);
  CHECK(fbs_goap_action_find(NULL, "chop", 4u, &act) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_find(d, NULL, 4u, &act) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_find(d, "chop", 4u, NULL) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_key(NULL, chop, &key, &klen) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_key(d, (fbs_goap_action)77u, &key, &klen) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_key(d, FBS_GOAP_ACTION_NONE, &key, &klen) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_cost(NULL, chop, &cost) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_cost(d, chop, NULL) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_cost(d, (fbs_goap_action)77u, &cost) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_pre(NULL, chop, wood, FBS_GOAP_EQ, 1) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_pre(d, (fbs_goap_action)77u, wood, FBS_GOAP_EQ, 1) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_pre(d, chop, (fbs_goap_atom)77u, FBS_GOAP_EQ, 1) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_pre(d, chop, wood, 6, 1) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_pre(d, chop, wood, -1, 1) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_effect(NULL, chop, wood, FBS_GOAP_SET, 1) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_effect(d, (fbs_goap_action)77u, wood, FBS_GOAP_SET, 1) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_effect(d, chop, (fbs_goap_atom)77u, FBS_GOAP_SET, 1) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_effect(d, chop, wood, 2, 1) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_effect(d, chop, wood, -1, 1) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_conditions(NULL, chop, conds, 4u, &n) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_conditions(d, chop, conds, 4u, NULL) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_conditions(d, chop, NULL, 4u, &n) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_conditions(d, (fbs_goap_action)77u, conds, 4u, &n) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_effects(NULL, chop, effs, 4u, &n) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_effects(d, chop, effs, 4u, NULL) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_effects(d, chop, NULL, 4u, &n) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_effects(d, (fbs_goap_action)77u, effs, 4u, &n) == FBS_GOAP_E_INVALID);

  /* states before the seal */
  CHECK(fbs_goap_state_init(d, sb.w, sizeof sb.w, NULL) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_init(NULL, sb.w, sizeof sb.w, &st) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_domain_seal(d) == FBS_GOAP_OK);

  st = state_new_defaults(d, &sb);
  CHECK(fbs_goap_state_init(d, NULL, 4u, &st) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_init(d, sb.w, 1u, &st) == FBS_GOAP_E_INVALID); /* short buffer */
  misaligned = raw + ((4u - ((size_t)(uintptr_t)raw & 3u)) & 3u) + 1u;
  CHECK(((size_t)(uintptr_t)misaligned & 3u) != 0u);
  CHECK(fbs_goap_state_init(d, misaligned, 64u, &st) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_init_defaults(d, misaligned, 64u, &st) == FBS_GOAP_E_INVALID);
  st = state_new_defaults(d, &sb);

  CHECK(fbs_goap_state_copy(NULL, st, st) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_copy(d, NULL, st) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_copy(d, st, NULL) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_set(NULL, st, wood, 1) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_set(d, NULL, wood, 1) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_set(d, st, (fbs_goap_atom)77u, 1) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_set(d, st, wood, 11) == FBS_GOAP_E_RANGE);
  CHECK(fbs_goap_state_set(d, st, wood, -1) == FBS_GOAP_E_RANGE);
  CHECK(fbs_goap_state_unset(NULL, st, wood) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_unset(d, NULL, wood) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_unset(d, st, (fbs_goap_atom)77u) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_known(NULL, st, wood) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_known(d, NULL, wood) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_known(d, st, (fbs_goap_atom)77u) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_get(NULL, st, wood, &v) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_get(d, NULL, wood, &v) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_get(d, st, wood, NULL) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_get(d, st, (fbs_goap_atom)77u, &v) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_equal(NULL, st, st) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_equal(d, NULL, st) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_equal(d, st, NULL) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_equal(d, st, st) == 1);
  CHECK(fbs_goap_apply(NULL, st, chop) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_apply(d, NULL, chop) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_apply(d, st, (fbs_goap_action)77u) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_applicable(NULL, st, chop) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_applicable(d, NULL, chop) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_applicable(d, st, (fbs_goap_action)77u) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_action_applicable(d, st, chop) == 1); /* no preconditions */

  conds[0] = mk_cond(wood, FBS_GOAP_EQ, 0);
  CHECK(fbs_goap_state_satisfies(NULL, st, conds, 1u) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_satisfies(d, NULL, conds, 1u) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_satisfies(d, st, NULL, 1u) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_state_satisfies(d, st, NULL, 0u) == 1); /* vacuously true */
  conds[0].atom = 77u;
  CHECK(fbs_goap_state_satisfies(d, st, conds, 1u) == FBS_GOAP_E_INVALID);
  conds[0].atom = wood;
  conds[0].cmp = 9u;
  CHECK(fbs_goap_state_satisfies(d, st, conds, 1u) == FBS_GOAP_E_INVALID);
  conds[0] = mk_cond(wood, FBS_GOAP_EQ, 0);

  /* planner */
  CHECK(fbs_goap_planner_create(NULL, NULL, NULL, &p) == FBS_GOAP_E_INVALID);
  CHECK(fbs_goap_planner_create(d, NULL, NULL, NULL) == FBS_GOAP_E_INVALID);
  {
    fbs_goap_planner *tmp = (fbs_goap_planner *)0x1;
    pcfg = fbs_goap_planner_config_default();
    pcfg.max_nodes = 0u;
    CHECK(fbs_goap_planner_create(d, &pcfg, NULL, &tmp) == FBS_GOAP_E_INVALID);
    pcfg = fbs_goap_planner_config_default();
    pcfg.max_nodes = (1u << 22) + 1u;
    CHECK(fbs_goap_planner_create(d, &pcfg, NULL, &tmp) == FBS_GOAP_E_INVALID);
    pcfg = fbs_goap_planner_config_default();
    pcfg.max_depth = 0u;
    CHECK(fbs_goap_planner_create(d, &pcfg, NULL, &tmp) == FBS_GOAP_E_INVALID);
    pcfg = fbs_goap_planner_config_default();
    pcfg.max_depth = 65536u;
    CHECK(fbs_goap_planner_create(d, &pcfg, NULL, &tmp) == FBS_GOAP_E_INVALID);
    CHECK(tmp == (fbs_goap_planner *)0x1);
  }
  {
    fbs_goap_domain *unsealed = make_domain();
    fbs_goap_planner *tmp = (fbs_goap_planner *)0x1;
    (void)atom_add(unsealed, "x", 0, 1, 0);
    CHECK(fbs_goap_planner_create(unsealed, NULL, NULL, &tmp) == FBS_GOAP_E_STATE);
    CHECK(tmp == (fbs_goap_planner *)0x1);
    fbs_goap_domain_destroy(unsealed);
  }
  CHECK(fbs_goap_planner_create(d, NULL, NULL, &p) == FBS_GOAP_OK);

  /* plan */
  {
    fbs_goap_request req = mk_request(st, conds, 1u, FBS_GOAP_H_ZERO);
    fbs_goap_action plan[4];
    fbs_goap_result res;
    fbs_goap_request bad;

    memset(&res, 0xA5, sizeof res);
    CHECK(fbs_goap_plan(NULL, &req, plan, 4u, &res) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_plan(p, NULL, plan, 4u, &res) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_plan(p, &req, plan, 4u, NULL) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_plan(p, &req, NULL, 4u, &res) == FBS_GOAP_E_INVALID);
    CHECK(untouched(&res, sizeof res, 0xA5));

    bad = req;
    bad.start = NULL;
    CHECK(fbs_goap_plan(p, &bad, plan, 4u, &res) == FBS_GOAP_E_INVALID);
    bad = req;
    bad.goal = NULL;
    CHECK(fbs_goap_plan(p, &bad, plan, 4u, &res) == FBS_GOAP_E_INVALID);
    bad = req;
    bad.goal_len = 0u;
    CHECK(fbs_goap_plan(p, &bad, plan, 4u, &res) == FBS_GOAP_E_INVALID);
    bad = req;
    bad.heuristic = 2;
    CHECK(fbs_goap_plan(p, &bad, plan, 4u, &res) == FBS_GOAP_E_INVALID);
    bad = req;
    bad.heuristic = -1;
    CHECK(fbs_goap_plan(p, &bad, plan, 4u, &res) == FBS_GOAP_E_INVALID);
    bad = req;
    bad.max_nodes = 4097u; /* beyond the planner capacity */
    CHECK(fbs_goap_plan(p, &bad, plan, 4u, &res) == FBS_GOAP_E_INVALID);
    bad = req;
    bad.max_depth = 65536u;
    CHECK(fbs_goap_plan(p, &bad, plan, 4u, &res) == FBS_GOAP_E_INVALID);
    bad = req;
    {
      fbs_goap_cond badgoal[1];
      badgoal[0] = mk_cond((fbs_goap_atom)77u, FBS_GOAP_EQ, 1);
      bad.goal = badgoal;
      CHECK(fbs_goap_plan(p, &bad, plan, 4u, &res) == FBS_GOAP_E_INVALID);
      badgoal[0] = mk_cond(wood, 9, 1);
      CHECK(fbs_goap_plan(p, &bad, plan, 4u, &res) == FBS_GOAP_E_INVALID);
    }
    CHECK(untouched(&res, sizeof res, 0xA5));

    /* plan_validate */
    {
      size_t fi = 0;
      int met = 0;
      fbs_goap_action steps[2];
      steps[0] = chop;
      steps[1] = chop;
      CHECK(fbs_goap_plan_validate(NULL, st, steps, 2u, conds, 1u, NULL, NULL, &fi, &met) ==
            FBS_GOAP_E_INVALID);
      CHECK(fbs_goap_plan_validate(p, NULL, steps, 2u, conds, 1u, NULL, NULL, &fi, &met) ==
            FBS_GOAP_E_INVALID);
      CHECK(fbs_goap_plan_validate(p, st, NULL, 2u, conds, 1u, NULL, NULL, &fi, &met) ==
            FBS_GOAP_E_INVALID);
      CHECK(fbs_goap_plan_validate(p, st, steps, 2u, NULL, 1u, NULL, NULL, &fi, &met) ==
            FBS_GOAP_E_INVALID);
      CHECK(fbs_goap_plan_validate(p, st, steps, 2u, conds, 1u, NULL, NULL, NULL, &met) ==
            FBS_GOAP_E_INVALID);
      CHECK(fbs_goap_plan_validate(p, st, steps, 2u, conds, 1u, NULL, NULL, &fi, NULL) ==
            FBS_GOAP_E_INVALID);
      steps[1] = (fbs_goap_action)77u;
      CHECK(fbs_goap_plan_validate(p, st, steps, 2u, conds, 1u, NULL, NULL, &fi, &met) ==
            FBS_GOAP_E_INVALID);
      /* an empty plan is legal: nothing is invalid and the goal is judged as is */
      CHECK(fbs_goap_plan_validate(p, st, NULL, 0u, conds, 1u, NULL, NULL, &fi, &met) ==
            FBS_GOAP_OK);
      CHECK(fi == 0u);
      CHECK(met == 1); /* wood == 0 holds in the default state */
    }
  }

  /* serialization */
  {
    unsigned char buf[512];
    size_t out = 0;
    fbs_goap_domain *g = NULL;
    CHECK(fbs_goap_domain_serialize(NULL, buf, sizeof buf, &out) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_domain_serialize(d, buf, sizeof buf, NULL) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_domain_serialize(d, NULL, 4u, &out) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_domain_serialize(d, NULL, 0u, &out) == FBS_GOAP_E_TRUNCATED);
    CHECK(out == fbs_goap_domain_serialized_size(d));
    CHECK(fbs_goap_domain_deserialize(NULL, 10u, NULL, NULL, &g) == FBS_GOAP_E_INVALID);
    CHECK(fbs_goap_domain_deserialize(buf, 10u, NULL, NULL, NULL) == FBS_GOAP_E_INVALID);
  }

  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(d);
}

/* ------------------------------------------------------------------------- */
/* Status names, version, config defaults                                    */
/* ------------------------------------------------------------------------- */

static void test_status_names(void) {
  CHECK(strcmp(fbs_goap_status_name(FBS_GOAP_OK), "ok") == 0);
  CHECK(strcmp(fbs_goap_status_name(FBS_GOAP_E_INVALID), "invalid") == 0);
  CHECK(strcmp(fbs_goap_status_name(FBS_GOAP_E_NOT_FOUND), "not_found") == 0);
  CHECK(strcmp(fbs_goap_status_name(FBS_GOAP_E_EXISTS), "exists") == 0);
  CHECK(strcmp(fbs_goap_status_name(FBS_GOAP_E_FULL), "full") == 0);
  CHECK(strcmp(fbs_goap_status_name(FBS_GOAP_E_RANGE), "range") == 0);
  CHECK(strcmp(fbs_goap_status_name(FBS_GOAP_E_SCHEMA), "schema") == 0);
  CHECK(strcmp(fbs_goap_status_name(FBS_GOAP_E_TRUNCATED), "truncated") == 0);
  CHECK(strcmp(fbs_goap_status_name(FBS_GOAP_E_SEALED), "sealed") == 0);
  CHECK(strcmp(fbs_goap_status_name(FBS_GOAP_E_STATE), "state") == 0);
  CHECK(strcmp(fbs_goap_status_name(FBS_GOAP_E_MEMORY), "memory") == 0);
  CHECK(strcmp(fbs_goap_status_name(-999), "unknown") == 0);
  CHECK(strcmp(fbs_goap_status_name(999), "unknown") == 0);
  CHECK(fbs_goap_version() == FBS_GOAP_VERSION);
  CHECK(fbs_goap_version() == 100u);
  CHECK(FBS_GOAP_COST_MAX == 0x3FFFFFFF);
  CHECK(FBS_GOAP_ATOM_NONE == (fbs_goap_atom)0xFFFFu);
  CHECK(FBS_GOAP_ACTION_NONE == (fbs_goap_action)0xFFFFu);
  {
    fbs_goap_config cfg = fbs_goap_config_default();
    fbs_goap_planner_config pcfg = fbs_goap_planner_config_default();
    CHECK(cfg.max_atoms == 64u);
    CHECK(cfg.max_actions == 64u);
    CHECK(cfg.max_conditions == 512u);
    CHECK(cfg.max_effects == 512u);
    CHECK(cfg.max_key_bytes == 4096u);
    CHECK(pcfg.max_nodes == 4096u);
    CHECK(pcfg.max_depth == 64u);
  }
}

/* ------------------------------------------------------------------------- */
/* Golden fixtures: the sealed soldier domain and its two plans              */
/* ------------------------------------------------------------------------- */

static void write_or_compare(const char *path, const unsigned char *bytes, size_t len,
                             const char *what) {
  FILE *fp;
  if (g_write_fixtures) {
    fp = fopen(path, "wb");
    ++g_checks;
    if (!fp) {
      ++g_fails;
      printf("FAIL cannot open %s for writing\n", path);
      return;
    }
    {
      size_t wrote = fwrite(bytes, 1u, len, fp);
      fclose(fp);
      CHECK(wrote == len);
      printf("wrote %s (%lu bytes)\n", path, (unsigned long)len);
    }
    return;
  }
  fp = fopen(path, "rb");
  ++g_checks;
  if (!fp) {
    ++g_fails;
    printf("FAIL cannot open fixture %s (run with --write-fixtures to create it)\n", path);
    return;
  }
  {
    unsigned char golden[4096];
    size_t got = fread(golden, 1u, sizeof golden, fp);
    fclose(fp);
    ++g_checks;
    if (got != len) {
      ++g_fails;
      printf("FAIL %s: %s is %lu bytes, expected %lu\n", path, what, (unsigned long)got,
             (unsigned long)len);
      return;
    }
    CHECK(memcmp(golden, bytes, len) == 0);
  }
}

static void test_fixtures(void) {
  soldier s;
  state_buf sb;
  fbs_goap_state *start;
  fbs_goap_planner *p = NULL;
  fbs_goap_action plan[8];
  fbs_goap_result res;
  fbs_goap_cond goal[2];
  fbs_goap_request req;
  unsigned char *blob;
  size_t len = 0;
  char path[512];
  char text[256];
  size_t text_len = 0;
  char keys[128];

  soldier_build(&s, 1, 1, 0);
  blob = serialize_alloc(s.d, &len);
  sprintf(path, "%s/soldier.bin", g_fixture_dir);
  write_or_compare(path, blob, len, "soldier domain blob");

  /* the committed bytes must still load and re-serialize identically */
  if (!g_write_fixtures) {
    FILE *fp = fopen(path, "rb");
    if (fp) {
      unsigned char golden[4096];
      size_t got = fread(golden, 1u, sizeof golden, fp);
      fclose(fp);
      if (got == len) {
        fbs_goap_domain *g = NULL;
        size_t l2 = 0;
        unsigned char *b2;
        CHECK(fbs_goap_domain_deserialize(golden, got, NULL, NULL, &g) == FBS_GOAP_OK);
        b2 = serialize_alloc(g, &l2);
        CHECK(l2 == len && memcmp(b2, golden, len) == 0);
        free(b2);
        fbs_goap_domain_destroy(g);
      }
    }
  }

  start = soldier_start(&s, &sb);
  CHECK(fbs_goap_planner_create(s.d, NULL, NULL, &p) == FBS_GOAP_OK);

  goal[0] = mk_cond(s.enemyalive, FBS_GOAP_EQ, 0);
  req = mk_request(start, goal, 1u, FBS_GOAP_H_ZERO);
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_FOUND);
  plan_to_keys(s.d, plan, res.plan_len, keys, sizeof keys);
  text_len = (size_t)sprintf(text, "%s\n", keys);

  goal[1] = mk_cond(s.alive, FBS_GOAP_EQ, 1);
  req = mk_request(start, goal, 2u, FBS_GOAP_H_ZERO);
  CHECK(fbs_goap_plan(p, &req, plan, 8u, &res) == FBS_GOAP_OK);
  CHECK(res.outcome == FBS_GOAP_FOUND);
  plan_to_keys(s.d, plan, res.plan_len, keys, sizeof keys);
  text_len += (size_t)sprintf(text + text_len, "%s\n", keys);

  sprintf(path, "%s/soldier-plan.txt", g_fixture_dir);
  write_or_compare(path, (const unsigned char *)text, text_len, "soldier plans");

  free(blob);
  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(s.d);
}

/* ------------------------------------------------------------------------- */

int main(int argc, char **argv) {
  int i;
  for (i = 1; i < argc; ++i) {
    if (strcmp(argv[i], "--write-fixtures") == 0) {
      g_write_fixtures = 1;
    } else if (strcmp(argv[i], "--fixture-dir") == 0 && i + 1 < argc) {
      g_fixture_dir = argv[++i];
    } else {
      printf("usage: %s [--write-fixtures] [--fixture-dir DIR]\n", argv[0]);
      return 2;
    }
  }

  test_t1_soldier_plans();
  test_t2_unsolvable_vs_node_cap();
  test_t3_cost_preference();
  test_t4_replanning();
  test_t5_bounded_search();
  test_t6a_repeatable();
  test_t6b_row_order_irrelevant();
  test_t6c_tie_order();
  test_t7_numeric_state();
  test_goap1_depth_cap_optimality();
  test_t8_heuristic_admissibility();
  test_t9_cost_validation();
  test_t10_reentrancy();
  test_t11_proc_pre();
  test_t12_state_schema();
  test_t13_already_satisfied();
  test_t15_truncation_and_capacity();
  test_t16_serialization();
  test_domain_clear();
  test_wide_domain();
  test_invalid_arguments();
  test_status_names();
  test_fixtures();

  printf("goap: %d checks passed, %d failed\n", g_checks - g_fails, g_fails);
  return g_fails > 100 ? 100 : g_fails;
}
