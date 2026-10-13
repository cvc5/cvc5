# cvc5 Proof Production: end-to-end pipeline

Focus: the API `ProofNode` data structure (what `Solver::getProof` returns)
and the **CPC** (Cooperating Proof Calculus / Eunoia) output path, the default
since cvc5 1.2 (`proofFormatMode = CPC` in `src/options/proof_options.toml`).
LFSC/Alethe/dot are sibling printers, mentioned only in passing.

Top-down: option → entry point → SAT proof → preprocessing proof → theory
proof → assembly → CPC output → recipe for a new theory.

---

## 1. Options and entry points

### Option flags

`src/options/proof_options.toml` declares the proof-relevant options:

| Option | Values | Effect |
|---|---|---|
| `--produce-proofs` | bool | turns on proof recording in every component |
| `--proof-format-mode` | `none, dot, lfsc, alethe, cpc` | which printer runs at the end (default **cpc**) |
| `--proof-check` | `eager, eager_simple, lazy, none` | when `ProofChecker` validates a step (per step or only at the end) |
| `--proof-granularity-mode` | `macro, rewrite, theory_rewrite, dsl_rewrite, dsl_rewrite_strict` | controls how aggressively `ProofPostprocess` expands `MACRO_*` rules |
| `--check-proofs` / `--check-proof-steps` | bool | runs `ProofChecker::check` on the final proof; `--check-proof-steps` re-checks each non-macro step in expanded form |
| `--prop-proof-mode` | `proof, sat_external_prove` | whether the SAT layer produces a real resolution proof or a single trusted step |

### API surface

The user-facing API is in `include/cvc5/cvc5.h` backed by
`src/api/cpp/cvc5.cpp`, which forwards to `src/smt/solver_engine.h`:

```cpp
// SolverEngine
std::vector<std::shared_ptr<ProofNode>>
getProof(modes::ProofComponent c = modes::ProofComponent::FULL);
```

`modes::ProofComponent` is the proof slice you want:

- `RAW_PREPROCESS` — just the per-assertion preprocessing proofs
- `PREPROCESS`     — preprocessing including theory preprocessing
- `SAT`            — propositional refutation, leaves are preprocessed clauses
- `THEORY_LEMMAS`  — proofs of theory lemmas added to SAT
- `FULL`           — the whole tree, ASSUME-leaves = original input assertions

The `std::vector` is so `THEORY_LEMMAS` / `RAW_PREPROCESS` can return one
`ProofNode` per assertion/lemma.

For the API, the single most important data structure is `ProofNode` — it
*is* the proof you receive.

---

## 2. The API data structure: `ProofNode`

`src/proof/proof_node.h`:

```cpp
class ProofNode {
  ProofRule d_rule;                                       // which inference rule
  std::vector<std::shared_ptr<ProofNode>> d_children;     // premises (subproofs)
  std::vector<Node> d_args;                               // rule-specific arguments
  Node d_proven;                                          // cached conclusion formula
};
```

Every step is `(rule, children, args) ⊢ d_proven`. The proof is a DAG
(`shared_ptr` lets subproofs be shared), with leaves being either
`ASSUME(F)` (open assumption) or 0-ary rules. The whole refutation is
rooted at a `SCOPE` node whose argument list is the original assertions
and whose conclusion is `false` — i.e.
`(SCOPE [a1...an] (… ⊢ false)) ⊢ ¬(a1 ∧ … ∧ an)`.

The enum `ProofRule` lives in `include/cvc5/cvc5_proof_rule.h` and is a
public C++ API enum (you can pattern-match on it from a client). It is
partitioned roughly into:

- **Core**: `ASSUME`, `SCOPE`
- **Equality / congruence**: `REFL`, `SYMM`, `TRANS`, `CONG`, `TRUE_INTRO`, `EQ_RESOLVE`, …
- **Boolean / CNF**: `RESOLUTION`, `CHAIN_RESOLUTION`, `FACTORING`, `REORDERING`, the Tseitin family `CNF_AND_POS`, `CNF_OR_NEG`, `CNF_ITE_*`, …
- **Substitution / rewriting**: `SUBS`, `REWRITE`, `EVALUATE`, `MACRO_SR_PRED_INTRO`, `MACRO_SR_PRED_TRANSFORM`, `MACRO_SR_EQ_INTRO`, …
- **Theory rules**: per-theory blocks (`ARITH_*`, `BV_*`, `STRINGS_*`, `ARRAYS_*`, `DT_*`, `QUANT_*`, …)
- **Trust escapes**: `TRUST` (with a `TrustId` tag) and `THEORY_REWRITE`, used when a step isn't yet refined to a checkable rule

There is also a sibling `ProofRewriteRule` enum (in the same header, for
granular rewrites used by `DSL_REWRITE`) and a `TrustId` enum in
`src/proof/trust_id.h` tagging *why* a `TRUST` step exists (e.g.
`THEORY_LEMMA`, `THEORY_INFERENCE_ARITH`, `PREPROCESS_BV_GAUSS`).

### Helpers around `ProofNode`

These are not what `getProof` returns, but they're how proofs are *built*:

- `ProofNodeManager` (`src/proof/proof_node_manager.h`) — only legal way to construct a `ProofNode`. `mkNode(rule, children, args, expected)` runs `ProofChecker::check` if `--proof-check=eager` and stores `d_proven`. `mkAssume`, `mkScope`, `mkTrust` are sugar.
- `ProofChecker` + `ProofRuleChecker` (`src/proof/proof_checker.h`, `src/proof/proof_rule_checker.h`) — a registry mapping each `ProofRule` to the checker that knows its semantics. Each theory installs its own checkers.
- `CDProof` (`src/proof/proof.h`) — context-dependent `fact ↦ ProofNode` map; `addStep(conc, rule, premiseFacts, args)` records a step and auto-links premises by fact name (placeholder `ASSUME` nodes that get spliced when `getProofFor(top)` is called).
- `LazyCDProof` (`src/proof/lazy_proof.h`) — `CDProof` + a `fact ↦ ProofGenerator*` table. Open `ASSUME` leaves are filled in by calling the generator at `getProofFor` time; this is what theories use so they don't have to materialize proofs eagerly.
- `EagerProofGenerator` (`src/proof/eager_proof_generator.h`) — opposite tactic: store the finished `ProofNode` at lemma-send time; lookup is a hash map.
- `ProofGenerator` (abstract base in `src/proof/proof_generator.h`) — the contract is `getProofFor(fact) → shared_ptr<ProofNode>`; everything that produces a proof of a particular fact implements this.
- `TrustNode` (`src/proof/trust_node.h`) — the *currency* used between components: `(kind, formula, ProofGenerator*)`. Kinds are `LEMMA`, `CONFLICT`, `PROP_EXP`, `REWRITE`. A theory hands a `TrustNode` to the inference manager; the generator will be queried later, lazily.
- `TheoryProofStepBuffer` (`src/proof/theory_proof_step_buffer.h`) — convenience for building macro substitution/rewrite chains step-by-step, then dumping into a `CDProof`.

Visualize the relationships:

```
TrustNode ──▶ ProofGenerator ──▶ ProofNode (built via ProofNodeManager,
                                            checked by ProofChecker)
              │  EagerProofGenerator   (precomputed)
              │  LazyCDProof / CDProof (incremental, indexed by fact)
              │  PreprocessProofGenerator, TConvProofGenerator, ProofEqEngine, …
```

---

## 3. Top-level orchestration: `PfManager`

`src/smt/proof_manager.h` (and `.cpp`) is the conductor. It is owned by
`Env` and contains:

```cpp
std::unique_ptr<ProofChecker>             d_pchecker;   // global rule checker
std::unique_ptr<ProofNodeManager>         d_pnm;        // global proof builder
std::unique_ptr<ProofPostprocess>         d_pfpp;       // expansion / elimination
std::unique_ptr<PreprocessProofGenerator> d_pppg;       // preprocessing proofs
std::unique_ptr<ProofLogger>              d_plog;       // streamed logging
ProofFinalCallback                        d_finalCb;    // final stats / checks
```

The two key methods:

```cpp
std::shared_ptr<ProofNode> connectProofToAssertions(
    std::shared_ptr<ProofNode> pfn, Assertions& as,
    ProofScopeMode scopeMode = ProofScopeMode::UNIFIED);

void checkFinalProof(std::shared_ptr<ProofNode> pfn);
```

`connectProofToAssertions` is the splicing step: the SAT proof's leaves
are `ASSUME(<preprocessed assertion>)`, and `PreprocessProofGenerator`
knows how each preprocessed assertion is derived from an original input.
`PfManager` walks the SAT proof, replaces each preprocessed-assertion
leaf with the preprocessing subproof, then wraps in a `SCOPE` over the
original inputs.

Then `ProofPostprocess` walks the resulting tree once more and
rewrites/expands rules to whatever granularity `--proof-granularity-mode`
requested. `MACRO_SR_PRED_TRANSFORM`, for instance, is exploded into
`SUBS` + `REWRITE` + `EQ_RESOLVE`, and at the strictest level individual
`REWRITE`s become DSL `ProofRewriteRule` applications.

Pipeline summary, drawn:

```
  parser ──▶ assertions ─────▶ preprocessing ───▶ theory preprocessing
                                    │  (PreprocessProofGenerator
                                    │   accumulates a TrustNode chain)
                                    ▼
                              CnfStream / ProofCnfStream
                                    │  (Tseitin steps in a LazyCDProof)
                                    ▼
                           SAT (CDCL) + TheoryEngine
                                    │  conflict clauses with
                                    │  resolution proofs;
                                    │  theory lemmas inlined
                                    ▼
                            empty clause ⊢ ⊥
                                    │
                  PfManager::connectProofToAssertions
                                    │  splices preproc proofs
                                    │  + outer SCOPE
                                    ▼
                             ProofPostprocess
                                    │  expands MACROs to chosen granularity
                                    ▼
              std::shared_ptr<ProofNode>  ←─── what API getProof() returns
                                    │
                                    ▼
                  AlethePrinter / LfscPrinter / EoPrinter (CPC) / DotPrinter
```

---

## 4. Preprocessing & rewriter proofs

### Preprocessing passes

A preprocessing pass derives from `PreprocessingPass`
(`src/preprocessing/preprocessing_pass.h`) and edits an
`AssertionPipeline`. Whenever it rewrites assertion `i` from `A` to
`A'`, it must call (eventually) `pppg->notifyPreprocessed(A, A', pg)`
on the `PreprocessProofGenerator`
(`src/smt/preprocess_proof_generator.h`), where `pg` is a generator for
the equality `A = A'` (or implication `A ⇒ A'`, depending on the pass).

`PreprocessProofGenerator::getProofFor(A')` walks back through the chain
of `notifyPreprocessed` records and assembles a single `ProofNode`
proving `A'` from the original `A` plus the rewrite proofs.

The most common building block is `TrustSubstitutionMap`
(`src/theory/trust_substitutions.h`), which is a `SubstitutionMap` that
*also* implements `ProofGenerator`: every `(x, t)` substitution comes
with a proof of `x = t`, and `applyTrusted(n)` returns a `TrustNode`
for `n = n[x↦t]`.

### Rewriter

`src/theory/rewriter.h` has two rewrite paths:

```cpp
Node       rewrite(TNode n);                                 // no proof
TrustNode  rewriteWithProof(TNode n, TConvProofGenerator* tcpg = nullptr);
```

`TConvProofGenerator` (term-conversion proof generator,
`src/proof/conv_proof_generator.h`) records every applied rewrite step
as a small `(lhs, rhs, ProofRule)` tuple, then assembles them via
`CONG` + `TRANS` into a single proof of `n = nrew`. The atomic steps
come from:

- `ProofRule::REWRITE` / `MACRO_REWRITE` for the RARE-DSL rules in `src/theory/rewrites.toml`
- `ProofRule::EVALUATE` for constant folding
- `ProofRule::THEORY_REWRITE` for theory-specific rewrites that don't yet have a DSL rule (this is a "trusted" escape hatch)

This is exactly where `--proof-granularity-mode` bites: at `MACRO` you
keep `MACRO_SR_*`, at `DSL_REWRITE_STRICT` every rewrite must be a
checkable `ProofRewriteRule` application.

---

## 5. Theory engine and theory solvers

### Plumbing

`src/theory/theory_engine.h` routes inferences from individual theories
to the SAT solver. Each `Theory` owns a `TheoryInferenceManager`
(`src/theory/theory_inference_manager.h`). The proof-aware methods on
it are:

```cpp
// Lemmas
bool trustedLemma(const TrustNode& tlem, InferenceId id, LemmaProperty p);
bool lemmaExp(Node conc, InferenceId id, ProofRule pfr,
              const std::vector<Node>& exp,        // explained premises
              const std::vector<Node>& noExplain,  // raw premises
              const std::vector<Node>& args, …);

// Conflicts
void trustedConflict(TrustNode tconf, InferenceId id);
void conflictExp(InferenceId id, ProofRule pfr,
                 const std::vector<Node>& exp,
                 const std::vector<Node>& args);

// Equality-engine-derived conflicts/propagations
void conflictEqConstantMerge(TNode a, TNode b);
eq::ProofEqEngine* getProofEqEngine();
```

Two internal generators do the heavy lifting:

- `eq::ProofEqEngine` — a wrapper around `eq::EqualityEngine` that records the *proof of every merge*. When the equality engine reports `a = b` from congruence/closure, the proof is a chain of `CONG`/`TRANS`/`SYMM`/`REFL` steps over the input equalities, capped by the rule that introduced each input. This is what makes equality-driven theories "free" w.r.t. proofs.
- `InferenceManagerBuffered` — collects pending facts/lemmas across a check pass, then flushes them as `TrustNode`s in one go.

### Per-theory proof checker

Each theory has a `proof_checker.{h,cpp}` (e.g.
`src/theory/arith/proof_checker.h`) that subclasses `ProofRuleChecker`
and `registerTo(ProofChecker*)`s itself for that theory's rules. The
theory constructor calls this once.

### Theory lemmas as a unit

The "complete" route is for the inference manager to construct a
`TrustNode` whose generator is either an `EagerProofGenerator` (the
proof was built right now) or a `LazyCDProof` slot (the proof will be
built when the SAT solver actually needs it for refutation). The
fallback route is a `TRUST` step with `TrustId::THEORY_LEMMA` — that's
a one-line "trust me" placeholder that ProofChecker accepts but
`--check-proofs` will warn about at higher pedantic levels.

---

## 6. Propositional / SAT proofs

`src/prop/proof_cnf_stream.h` wraps `CnfStream`. When
`convertAndAssert(F, …, ProofGenerator* pg)` is called, every Tseitin
clause derived from `F` gets a proof in a `LazyCDProof`: the rule is
one of `CNF_AND_POS`, `CNF_OR_NEG`, `CNF_ITE_*`, etc., and at the top
sits whatever `pg` proves about `F`.

`src/prop/sat_proof_manager.h` (`SatProofManager`) hooks into
MiniSat-via-cvc5 and records, for every learnt clause, the chain of
resolutions (`CHAIN_RESOLUTION` rule) that produced it. When the SAT
solver finally derives the empty clause, the manager builds a single
`ProofNode` ending in `false` whose leaves are clauses from
`ProofCnfStream` (CNF-derived) or from theory lemmas (their
`TrustNode`s' generators).

`src/prop/prop_proof_manager.h` (`PropPfManager`) is the SMT-facing
wrapper: `getProof(connectCnf=true|false)` returns either the raw
SAT-only refutation or one with the Tseitin layer spliced.

`--prop-proof-mode=sat_external_prove` collapses this whole subtree
into one `TRUST` step (useful when piping to an external DRAT checker).

---

## 7. Final assembly and CPC output

`SolverEngine::getProof` (`src/smt/solver_engine.cpp`, around the
`getProof` definition) glues things together:

1. Ask `PropPfManager` for the SAT-level proof (with or without CNF splice).
2. If `c == FULL`, call `PfManager::connectProofToAssertions` to splice preprocessing and wrap in `SCOPE`.
3. Run `ProofPostprocess` per the granularity option.
4. Return the resulting `std::vector<std::shared_ptr<ProofNode>>` to the API caller.

If the user asked for a printed proof, `PfManager::printProof` then
dispatches on `ProofFormatMode`:

- `cpc`    → `src/proof/eo/eo_printer.h` (`EoPrinter`) plus `eo_post_processor` and `eo_node_converter`
- `alethe` → `src/proof/alethe/alethe_printer.h`
- `lfsc`   → `src/proof/lfsc/lfsc_printer.h`
- `dot`    → `src/proof/dot/dot_printer.h`

### CPC specifically

CPC ("Cooperating Proof Calculus") is cvc5's native external proof
format, written in **Eunoia** (the `eo` language). The shipped Eunoia
signatures live in `proofs/eo/` and the per-rule reference signatures
are loaded by the `eo` checker. Every `ProofRule` in the API enum
corresponds either to a checkable Eunoia rule (1:1) or to a macro that
the post-processor must expand before printing.

What this means for you as a theory implementer: **for your new rule to
be CPC-compatible, you must give it (a) a `ProofRuleChecker::checkInternal`
implementation in C++, and (b) a corresponding rule in an Eunoia
signature file under `proofs/eo/cvc5/theories/` (or similar).**
`EoPrinter` will simply print
`(step <id> <conc> :rule <name> :premises (...) :args (...))`, and the
external `eo` checker will validate it against your signature. If you
skip the signature, the printer will emit the rule but the external
checker will reject it.

If your rule ends up emitted as a `TRUST` step, CPC will print
`:rule trust` and the external checker treats it as an axiom — fine for
prototyping, not fine for a verified pipeline.

---

## 8. Subsolvers

`src/theory/smt_engine_subsolver.h` creates a fresh `SolverEngine` for
things like quantifier instantiation (CEGQI), abduction, interpolation,
model-based instantiation, etc. The subsolver *can* be configured with
`--produce-proofs`, but currently the result that comes back to the
parent theory is typically used as a *fact*, not a proof: the theory
turns it into a lemma whose proof is a single `TRUST` step with an
appropriate `TrustId` (e.g. `THEORY_INFERENCE_QUANTIFIERS`).

There's no automatic "inline the subsolver's proof into the parent
proof" yet — if you need that, you have to call
`subSolver->getProof(FULL)`, transcribe it onto the parent's
`ProofNodeManager`, and emit it as a single composite step, treating
the subsolver's `SCOPE` over its assertions as the lemma you're
justifying.

---

## 9. Recipe: adding proofs to a new theory solver

Assume your theory `mytheory` produces (a) **theory lemmas** (clauses
to SAT), (b) **case splits**, and (c) results obtained from a
**subsolver call**. In all three cases, what you ship out the door is
a `TrustNode`. The proof story differs only in *what generator backs
the TrustNode*.

### Step 1 — declare proof rules in the public API

Edit `include/cvc5/cvc5_proof_rule.h`, in the theory rules block, e.g.:

```cpp
EVALUE(MYTHEORY_FOO),    // ⊢ foo from the conjunction of children
EVALUE(MYTHEORY_BAR),    // ⊢ bar premise; arg is the splitting term
```

Comment each rule with its conclusion schema; this comment is what the
auto-generated docs, `EoPrinter`, and the Eunoia signature must agree
with.

### Step 2 — implement the C++ checker

Create `src/theory/mytheory/proof_checker.{h,cpp}`:

```cpp
class MyTheoryProofRuleChecker : public ProofRuleChecker {
 public:
  MyTheoryProofRuleChecker(NodeManager* nm) : ProofRuleChecker(nm) {}
  void registerTo(ProofChecker* pc) override {
    pc->registerChecker(ProofRule::MYTHEORY_FOO, this);
    pc->registerChecker(ProofRule::MYTHEORY_BAR, this);
  }
 protected:
  Node checkInternal(ProofRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) override {
    if (id == ProofRule::MYTHEORY_FOO) {
      // validate shape of children/args and return the conclusion,
      // or Node::null() to reject
    }
    …
  }
};
```

Instantiate the checker in `TheoryMyTheory`'s constructor and call
`registerTo(d_env.getProofNodeManager()->getChecker())` if proofs are
enabled. Look at `src/theory/arith/proof_checker.cpp` as a template.

### Step 3 — write the Eunoia signature (CPC only)

Add a file under `proofs/eo/cvc5/theories/` with one
`(declare-rule …)` per new `ProofRule`. Take an existing theory file
(`Arith.eo`, `Bv.eo`, …) as a template. Match `:premises`/`:args` to
the *exact* shape you accept in `checkInternal`. This is the contract
`EoPrinter` will rely on. Without this,
`--proof-format-mode=cpc` will emit your rule but external checking
will fail.

### Step 4 — produce the proof at lemma-send time

Two patterns; pick per call site.

**Eager** (cheap and you have all the premises in hand):

```cpp
auto pnm = d_env.getProofNodeManager();
auto pf  = pnm->mkNode(ProofRule::MYTHEORY_FOO,
                       {childPf1, childPf2}, {arg0}, conc);
TrustNode tn = d_epg->mkTrustNode(conc, pf);  // EagerProofGenerator
d_im->trustedLemma(tn, InferenceId::MYTHEORY_FOO);
```

**Lazy** (you don't want to build the proof unless SAT actually uses
this lemma in the refutation):

```cpp
d_lazyPf->addStep(conc, ProofRule::MYTHEORY_FOO,
                  {child1Fact, child2Fact}, {arg0});
TrustNode tn = TrustNode::mkTrustLemma(conc, d_lazyPf.get());
d_im->trustedLemma(tn, InferenceId::MYTHEORY_FOO);
```

If you prefer to stay close to the equality engine, use
`inferManager->lemmaExp(conc, id, pfr, exp, noExplain, args)` and let
`ProofEqEngine` close the explained premises automatically — that's the
dominant pattern in arithmetic, arrays, and strings.

### Step 5 — case splits

A "split" is just a tautological lemma like `φ ∨ ¬φ` or
`x ≤ 0 ∨ x > 0`. Treat it like any other lemma: assemble a proof of
the disjunction (most splits are instances of a checkable propositional
or theory rule, e.g. `ARITH_SPLIT`), wrap in a `TrustNode`, send via
`trustedLemma`. The SAT solver makes the *decision*; the *split lemma*
is what carries proof content. If the split is just "by excluded
middle" you can use a generic `EXCLUDED_MIDDLE`-style rule (or, for
now, a tagged `TRUST` step with a clear `TrustId`).

### Step 6 — subsolver results

```cpp
std::unique_ptr<SolverEngine> sub;
initializeSubsolver(sub, d_env);
sub->assertFormula(query);
Result r = sub->checkSat();
if (r.isUnsat()) {
  // Two options:
  //  (a) trusted: emit as a single TRUST step
  TrustNode tn = TrustNode::mkTrustLemma(notQuery, /*pg=*/nullptr);
  d_im->trustedLemma(tn, InferenceId::MYTHEORY_SUBSOLVER);

  //  (b) inlined: pull the subsolver's proof, transcribe it onto your PNM
  auto subPfs = sub->getProof(modes::ProofComponent::FULL);
  // subPfs[0] is rooted at SCOPE([query]) ⊢ ¬query
  // Wrap/transcribe it through your ProofNodeManager so its leaves
  // become children of a fresh node concluding ¬query, then hand
  // back as a TrustNode with an EagerProofGenerator.
}
```

Path (b) is preferable for verifiability but requires that any rules
used inside the subsolver are also part of your CPC signature (almost
always true since both run cvc5).

### Step 7 — wire the rest

- Register the checker in your `TheoryMyTheory` constructor (guarded by `d_env.isProofProducing()` or equivalent).
- If you maintain a `TConvProofGenerator` or `ProofEqEngine`, pass it the checker so it can resolve rule conclusions.
- Add unit tests under `test/unit/theory/` and run with `--produce-proofs --check-proofs --proof-check=eager --proof-pedantic=100` so unproven branches blow up loudly.
- Add CPC end-to-end tests by running with `--produce-proofs --proof-format-mode=cpc -o proof` and piping the output through the `eo` checker against your new signature file.

### Granularity and trust budget

Pragmatically, you don't have to land everything fully refined in one
pass. Land the new rules at `MACRO` granularity first (i.e. allow
`MACRO_*` and `THEORY_REWRITE` to remain in your subproofs); then
iteratively reduce trust by adding (i) more granular per-step rules and
(ii) DSL rewrite rules in `src/theory/<your>/rewrites.toml` so
`--proof-granularity-mode=dsl_rewrite_strict` succeeds. This is the
same trajectory arithmetic and bitvectors followed.

---

## TL;DR for someone instrumenting a new theory

1. **Always emit a `TrustNode`.** Whether the proof is a `TRUST` placeholder or a fully refined `MYTHEORY_FOO` step is a knob you turn over time.
2. **Public-API touchpoint = `ProofRule` enum + `ProofNode` shape**, in `include/cvc5/cvc5_proof_rule.h` and `src/proof/proof_node.h`.
3. **CPC touchpoint = a matching `(declare-rule …)` in `proofs/eo/`** plus the C++ `ProofRuleChecker`. `EoPrinter` is mechanical; the Eunoia signature is the actual semantic contract.
4. **Splits and subsolver results are not special** at the proof layer: build a `TrustNode` like any other lemma, with the trust budget you can afford.
