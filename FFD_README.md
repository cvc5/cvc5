# Fixed first decisions in this cvc5 checkout

This checkout contains a draft cvc5 implementation of the fixed first
decisions (FFD) mechanism described in the FFD paper. The central
idea is to guide the SAT search into a partition without asserting the
partitioning formula. Because the original assertion set is unchanged, clauses
learned while exploring the partition are consequences of the original problem
and can be shared with other workers.

This repository contains the cvc5 side of that design: an FFD decision
strategy, ways to generate FFD inputs, and a plugin notification for reporting
that a partition is complete. It does **not** contain the full SMT-D broker that
the paper uses to launch workers, exchange clauses, count completed partitions,
and implement the FFD-P/FFD-PS/FFD-CS/FFD-CSV configurations.

## Paper-to-code map

### Algorithm 1: fixed first decisions

The main implementation is `DecisionStrategyFFD` in
`src/theory/decision_strategy.{h,cpp}`.

- `addLiteral()` rewrites each supplied Boolean term and calls
  `Valuation::ensureLiteral()` so that it has a SAT literal.
- `getNextDecisionRequest()` is called through cvc5's external decision
  machinery. If an FFD literal is unassigned, it returns that literal as the
  required next decision.
- The strategy is registered as `DecisionManager::STRAT_FFD`, the first entry
  in the decision-strategy ordering, so it takes precedence over the existing
  theory decision strategies.
- In normal mode, the strategy is consulted again after a backtrack or restart.
  If the FFD literal becomes unassigned, it is requested again. If it has been
  propagated false, the strategy stops requesting it and ordinary solving can
  continue. This is the behavior of Algorithm 1 in the paper.
- The API accepts a list rather than only one literal. In normal mode the
  implementation requests unassigned entries in list order; in
  `ffd-fast-partition-mode` the solver first combines the list into one `and`
  term.

`--ffd-once` is an experimental deviation from the paper. It stops using the
strategy after it has returned as many decisions as there are input literals,
so decisions undone later are not necessarily forced again.

### Entering FFD solving

`SolverEngine::checkSatFFD()` in `src/smt/solver_engine.cpp` creates the
strategy, adds the requested terms, registers it with the theory engine's
decision manager, and then calls the ordinary `checkSatInternal()` path. The
same input formula, preprocessing, SAT engine, and clause-learning path are
therefore used; the extra state is a decision strategy, not a set of asserted
partition clauses.

There are two usable entry points:

1. SMT-LIB extension:

   ```smt2
   (set-logic QF_UF)
   (declare-const a Bool)
   (assert (or a (not a)))
   (check-sat-ffd (a))
   ```

   The parser/token/command plumbing is in `src/parser/tokens.{h,cpp}`,
   `src/parser/smt2/smt2_cmd_parser.cpp`, and `src/parser/commands.{h,cpp}`.
   The grammar is `(check-sat-ffd (<term>*))`.

2. C++ API:

   ```cpp
   Result result = solver.checkSatFFD({decision1, decision2});
   ```

   The public declaration is in `include/cvc5/cvc5.h`; argument validation and
   conversion to internal nodes are in `src/api/cpp/cvc5.cpp`.

There is currently no corresponding C, Python, or Java `checkSatFFD` entry
point. The generic command printer also only emits an "unknown command"
placeholder for `check-sat-ffd`; parsing and execution work, but round-trip
command printing is incomplete.

### Algorithm 2: simulated partition solving

Pass `--ffd-partition-mode` to turn FFD into the simulated-partition behavior
from Algorithm 2. Once any member of the requested cube is known false, the
decision strategy sends a `false` lemma through its `OutputChannel`. This ends
the worker's current check with `unsat`. In this mode, that result means **the
FFD partition is unsatisfiable**, not necessarily that the original formula is
unsatisfiable.

For example, this formula is satisfiable overall but its `a` partition is not:

```smt2
(set-logic QF_UF)
(declare-const a Bool)
(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)
(assert (or (not a) x))
(assert (or (not a) (not x)))
(assert (or y z))
(assert (or (not y) (not z)))
(check-sat-ffd (a))
```

With the current build, it returns `sat` without a partition mode and `unsat`
with `--ffd-partition-mode`.

The false-literal check lives in `getNextDecisionRequest()`, so it only runs
when the SAT solver asks for another decision. There is no separate check at
the end of solving. This is important when experimenting with formulas that
preprocessing or propagation can solve without another decision request.

### Algorithms 3 and 4: collaborative solving hook

Pass `--ffd-fast-partition-mode` to use the collaborative hook. In this mode:

- `SolverEngine::checkSatFFD()` combines all requested terms into a single
  conjunction before making a SAT literal.
- When that conjunction is propagated false, `DecisionStrategyFFD` looks for a
  registered plugin whose name is exactly `LemmaTransceiver`.
- If found, it sends one `PARTITION_SOLVED` notification and continues solving
  the original problem. The callback currently carries an empty term vector.
- If no plugin with that exact name is present, the strategy falls back to
  injecting `false`, ending the worker as in partition-only mode.

The notification path spans:

- internal plugin API: `src/expr/plugin.h`;
- public C++ plugin API and internal/external conversion:
  `include/cvc5/cvc5.h` and `src/api/cpp/cvc5.cpp`;
- C plugin callback adapter: `include/cvc5/c/cvc5.h` and
  `src/api/c/cvc5_c_structs.{h,cpp}`.

In the current working tree this callback is an uncommitted generalization from
the committed `handlePartitionSolved()` method to
`notifyGeneral(NotificationType, terms)`. A coordinator can use it to count
partition completions while leaving the worker alive. The rest of Algorithm 4
- worker lifecycle, the all-partitions-complete condition, first whole-problem
result, timeouts, and clause transport - belongs in an external broker and is
not implemented here.

Do not enable `--ffd-partition-mode` and `--ffd-fast-partition-mode` together.
The former branch has precedence in `DecisionStrategyFFD`, while the latter
still changes input construction to a single conjunction.

## Generating decisions and cubes

The existing partition generator has three added strategy names in
`src/options/parallel_options.toml` and dispatch code in
`src/theory/partition_generator.cpp`:

- `ffd-list` collects `N` usable literals from the SAT decision trail and
  writes one literal per line.
- `ffd-cube` selects `log2(N)` decision literals and emits the `N` truth-table
  rows. Each row is a parenthesized term list suitable as the argument list of
  `check-sat-ffd`.
- `ffd-scatter` is exposed as an option, but its `ffd` parameter is currently
  unused by `makeScatterPartitions()`. It therefore follows the ordinary
  scatter-partition output path and should be considered unfinished as an FFD
  input generator.

A representative generation command is:

```sh
build/bin/cvc5 \
  --compute-partitions=8 \
  --partition-strategy=ffd-cube \
  --partition-when=climit \
  --checks-before-partition=1 \
  --write-partitions-to=ffd-cubes.txt \
  benchmark.smt2
```

The existing partition timing and selection options still apply, notably
`--partition-tlimit`, `--partition-start-time`,
`--partition-time-interval`, `--partition-when`,
`--checks-before-partition`, `--checks-between-partitions`,
`--partition-conflict-size`, and `--random-partitioning`.

Partition generation deliberately ends its generator run by returning a false
lemma. `src/smt/solver_engine_state.cpp` suppresses an expected-status mismatch
when `--compute-partitions` was set, because this `unsat` is a control result of
generation rather than the benchmark's logical status.

## Current maturity and extension points

At the time of this inspection, branch `fixed-first-decisions` is one commit
(`bea7ee8436`, "changes for draft PR") ahead of `upstream/main`. That commit
adds 469 lines across 22 files. Seven additional source/header files have
unstaged edits for the generalized plugin notification API.

The core production build in `build/` identifies itself as
`1.3.4.dev+ffd-for-PR@bea7ee8436-modified` and supports the parser command and
FFD options. Manual smoke checks confirmed all three important paths:

- ordinary FFD continues to a whole-problem `sat` result;
- `--ffd-partition-mode` can return `unsat` for an exhausted FFD partition;
- a C++ plugin named `LemmaTransceiver` receives `PARTITION_SOLVED`, after
  which the worker continues and returns the whole-problem result.

This is still draft research code rather than a merge-ready feature:

- There are no FFD regression/unit tests or user documentation under the
  tracked `test/`, `examples/`, or `docs/` trees.
- The build is a production build with unit tests disabled.
- The new C++ `Plugin::notifyGeneral()` is pure virtual, but the existing C++
  unit-test plugins and the Python and Java plugin adapters have not been
  updated to implement it. Those plugin subclasses are abstract in the current
  tree, so API/test builds that instantiate them need updates.
- `ffd-scatter` and command printing are incomplete, as described above.
- Collaborative operation depends on the hard-coded plugin name
  `LemmaTransceiver`, and the partition notification contains no partition ID
  or term payload.
- The repository has no implementation or configuration for the paper's SMT-D
  broker, clause-sharing policy, portfolio option schedules, benchmark
  selection, or result aggregation.

Good next steps for building on this work are to add minimal SMT-LIB and C++
regressions for restart/re-force behavior, partition completion, and plugin
continuation; make the notification callback backward-compatible and implement
it in all language adapters; remove the plugin-name coupling; finish
`ffd-scatter` and SMT-LIB printing; and add an external coordinator example that
maps generated cubes to workers and distinguishes `PARTITION_SOLVED` from a
whole-problem result.
