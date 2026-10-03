# fbs-goap

Goal-oriented action planning (GOAP) for game AI in C99, with bounded memory and deterministic plans.

## What it does

You describe a world as integer slots and a set of actions, give the planner a start state and a goal, and get back the cheapest sequence of actions that reaches the goal, in execution order.

- **Domain.** `fbs_goap_atom_add` registers a named `int32` slot with a `[min, max]` range and a default. `fbs_goap_action_add` registers an action with an integer cost. `fbs_goap_action_pre` adds preconditions (`EQ`, `NE`, `LT`, `LE`, `GT`, `GE`) and `fbs_goap_action_effect` adds effects (`SET`, or `ADD` clamped to the slot's range). `fbs_goap_domain_seal` freezes it.
- **State.** A state is a buffer you own, sized by `fbs_goap_state_size`. Each slot is either known or unknown, and an unknown slot never satisfies a condition.
- **Planning.** `fbs_goap_plan` runs a forward best-first search and returns `FBS_GOAP_OK` with an explicit outcome: `FOUND`, `ALREADY_SATISFIED`, `UNSOLVABLE` (proven), `NODE_CAP`, `DEPTH_CAP` or `PLAN_TRUNCATED`. A found plan is optimal among plans no longer than the depth cap.
- **Per-agent tuning.** A request can carry per-action cost overrides and a `proc_pre` callback that vetoes actions based on game data the symbolic state does not hold.
- **Replanning.** `fbs_goap_apply` applies one action's effects to a state, and `fbs_goap_plan_validate` reports the first step of an existing plan that can no longer run, and whether the plan still reaches the goal.
- **Serialization.** `fbs_goap_domain_serialize` and `fbs_goap_domain_deserialize` write and read a sealed domain as a versioned little-endian blob.

## When to use it

- NPC decision making where behaviour is "pick a goal, then find the steps", with tens of atoms and actions rather than thousands.
- You need the same plan on every machine and every run (replays, lockstep, tests).
- You want to know why planning stopped: proven impossible, out of nodes or out of depth are separate outcomes.
- You want a fixed memory budget per planner, with no allocation while planning.

## When not to use it

- **Large state spaces.** The search is over concrete states, so work grows with the number of reachable states. `tests/test_goap.c` (T-5) builds 14 independent toggles (16384 states): the default 4096-node planner reports `NODE_CAP`, and a 20000-node planner finds the 14-step plan after generating 16383 nodes.
- **Hard limits.** At most 4096 atoms and 4096 actions per domain, keys of 1 to 255 bytes, at most 4194304 (2^22) search nodes per planner and a depth cap of at most 65535. Defaults are 64 atoms, 64 actions, 512 preconditions, 512 effects and 4096 key bytes for a domain, and 4096 nodes with depth 64 for a planner.
- **Integers only.** Slot values and costs are integers (costs in `[0, 0x3FFFFFFF]`). There is no floating point anywhere in the library.
- **Two heuristics, no custom one.** `FBS_GOAP_H_ZERO` (uniform-cost search) or `FBS_GOAP_H_MAX_UNSAT` (admissible). You cannot plug in your own.
- **Simple effects.** One effect per action per atom, applied unconditionally. Hierarchical or partial-order planning is out of scope.
- **Fixed domains.** Registration ends at seal. Changing a domain means `fbs_goap_domain_clear` and rebuilding it, and a domain must outlive its planners and must not be cleared while they exist.
- **No threads inside.** Planning is single-threaded; parallelism is up to you (see Design notes).

## Example

A soldier that must find the enemy and load before it can aim and shoot. `FBS_GOAP_OK` is 0, so the setup calls are chained with `||`.

```c
#include <fbs/goap.h>
#include <stdint.h>
#include <stdio.h>

int main(void) {
  fbs_goap_domain *d = NULL;
  fbs_goap_planner *p = NULL;
  fbs_goap_state *start = NULL;
  fbs_goap_atom seen, loaded, aimed, alive;
  fbs_goap_action scout, load, aim, shoot, plan[8];
  fbs_goap_cond goal;
  fbs_goap_request req = {0};
  fbs_goap_result res;
  uint32_t buf[16]; /* 4-byte aligned; four atoms need 24 bytes */
  size_t i;
  int rc = 1;

  if (fbs_goap_domain_create(NULL, NULL, &d) != FBS_GOAP_OK) return 1;
  if (fbs_goap_atom_add(d, "seen", 4, 0, 1, 0, &seen) || fbs_goap_atom_add(d, "loaded", 6, 0, 1, 0, &loaded) ||
      fbs_goap_atom_add(d, "aimed", 5, 0, 1, 0, &aimed) || fbs_goap_atom_add(d, "alive", 5, 0, 1, 1, &alive) ||
      fbs_goap_action_add(d, "scout", 5, 1, &scout) || fbs_goap_action_effect(d, scout, seen, FBS_GOAP_SET, 1) ||
      fbs_goap_action_add(d, "load", 4, 1, &load) || fbs_goap_action_effect(d, load, loaded, FBS_GOAP_SET, 1) ||
      fbs_goap_action_add(d, "aim", 3, 1, &aim) || fbs_goap_action_pre(d, aim, seen, FBS_GOAP_EQ, 1) ||
      fbs_goap_action_pre(d, aim, loaded, FBS_GOAP_EQ, 1) || fbs_goap_action_effect(d, aim, aimed, FBS_GOAP_SET, 1) ||
      fbs_goap_action_add(d, "shoot", 5, 1, &shoot) || fbs_goap_action_pre(d, shoot, aimed, FBS_GOAP_EQ, 1) ||
      fbs_goap_action_effect(d, shoot, alive, FBS_GOAP_SET, 0) || fbs_goap_domain_seal(d) ||
      fbs_goap_state_init_defaults(d, buf, sizeof buf, &start) || fbs_goap_planner_create(d, NULL, NULL, &p))
    goto done;

  goal.atom = alive; goal.cmp = FBS_GOAP_EQ; goal.pad = 0; goal.value = 0;
  req.start = start; req.goal = &goal; req.goal_len = 1; req.heuristic = FBS_GOAP_H_MAX_UNSAT;
  if (fbs_goap_plan(p, &req, plan, 8, &res) != FBS_GOAP_OK || res.outcome != FBS_GOAP_FOUND) goto done;
  for (i = 0; i < res.plan_len; ++i) {
    const char *key; size_t len; /* keys are not NUL-terminated */
    if (fbs_goap_action_key(d, plan[i], &key, &len) != FBS_GOAP_OK) goto done;
    printf("%u. %.*s\n", (unsigned)(i + 1), (int)len, key);
  }
  printf("cost %d, %u nodes expanded\n", (int)res.plan_cost, res.nodes_expanded);
  rc = 0;
done:
  fbs_goap_planner_destroy(p);
  fbs_goap_domain_destroy(d);
  return rc;
}
```

It prints a four-step plan of cost 4. Build it as an executable that links `fbs::goap`, with this repository added through `add_subdirectory` or FetchContent (below).

## Build and test

Requires CMake 3.16+ and a C99 compiler. There are no dependencies beyond the standard C library and no vendored code. The CMake build links `m` on non-MSVC toolchains, though the planner itself makes no libm calls.

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DBUILD_TESTING=ON
cmake --build build --parallel 2
ctest --test-dir build --output-on-failure --no-tests=error
```

This runs two CTest tests. `goap` runs `tests/test_goap.c`, a self-contained test program covering optimal plans, proven unsolvability versus the node cap, depth-cap correctness, replanning and cost overrides, the `proc_pre` contract, `ADD` clamping, truncated outputs, every capacity limit, allocator failure, NULL and bad-enum arguments on every entry point, serialization round trips with 4000 random byte flips, and two golden fixtures in `tests/fixtures/goap/` (a serialized domain and its expected plans). `goap_example` runs `fbs_goap_example` (`examples/basic.c`), which creates a default domain and prints the API version.

Options: `FBS_BUILD_TESTS` and `FBS_BUILD_EXAMPLES`, both `ON` by default. `cmake --install` installs the library and header but no CMake package config file, so consume the library with `add_subdirectory` or FetchContent:

```cmake
include(FetchContent)
FetchContent_Declare(fbs_goap
  GIT_REPOSITORY https://github.com/finalbuildgames-com/fbs-goap.git
  GIT_TAG <full-commit-sha>) # pin a reviewed commit
FetchContent_MakeAvailable(fbs_goap)
target_link_libraries(your_target PRIVATE fbs::goap)
```

This repository ships the C library only. No engine adapters or language bindings are included.

## Design notes

- **Determinism.** Integer costs, no floating point, successors generated in ascending action id, and a total tie order (f ascending, g descending, insertion order ascending). `tests/test_goap.c` checks that 100 repeated plans are identical down to node counts (T-6a), that registering rows in reverse order gives a byte-identical domain and plan (T-6b), and that `H_MAX_UNSAT` matches uniform-cost search and a brute-force referee on 200 seeded random domains (T-8).
- **Memory.** A domain and a planner are each one allocation, made at create time through an optional `fbs_goap_allocator` (`malloc`/`free` when NULL). Nothing is allocated after create: planning and plan validation work inside the planner's block, and states live in buffers you provide. `fbs_goap_domain_memory` and `fbs_goap_planner_memory` report the block sizes.
- **Threading.** No globals or static mutable state. A sealed, const domain may be planned against by several planners concurrently. A planner holds search scratch, so use each planner from one thread at a time.
- **Errors.** Functions return `fbs_goap_status`, or an `int` that is negative on error; `fbs_goap_status_name` gives a short name. Errors leave outputs untouched, except `FBS_GOAP_E_TRUNCATED`, which reports the required size. `fbs_goap_plan` returns `FBS_GOAP_OK` whenever the search reached a conclusion, so always read `result.outcome`.
- **Versioning.** `FBS_GOAP_VERSION` and `fbs_goap_version()` report the API version (100). Public structs have no size fields. Serialized domains start with the magic `FBSG` and a schema version; `fbs_goap_domain_deserialize` rejects a wrong magic, version or length, or inconsistent contents, with `FBS_GOAP_E_SCHEMA`.

## License

MIT for Final Build Games' original code; see [LICENSE](LICENSE). The planner is an original C design. Its problem framing (atoms, actions with preconditions, effects and a cost, procedural preconditions, a node cap, replanning from the current state) comes from Narratech's GOAP NPC plugin (MIT, Copyright (c) 2026 Narratech Laboratories). No code from it is copied; its license is reproduced in [THIRD_PARTY_NOTICES](THIRD_PARTY_NOTICES) and `third_party/narratech/`.
