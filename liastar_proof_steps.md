# lia* proof infrastructure — change log

Record of the changes made to fix
`build/bin/cvc5 --check-proofs --proof-check=lazy paper2008.smt2`
and to give the lia* extension a lazy, subsolver-ready proof generator.

The fix has two independent parts:

1. A bug fix in the generic proof machinery for `STAR_CONTAINS`-style
   "closure but not really" kinds.
2. A lazy `ProofGenerator` for the three lia* lemmas (split,
   non-negativity, STAR_CONTAINS reduction), wired into
   `LiaStarExtension`.

---

## Part 1 — Closure-handling bug fix

### Symptom

```
$ build/bin/cvc5 --check-proofs --proof-check=lazy paper2008.smt2
Fatal failure within TConvProofGenerator::getProofForRewriting at
src/proof/conv_proof_generator.cpp:501
Check failure: cur[0] == ret[0]
```

The trace showed the failure occurring while building a congruence
proof for the original input assertion
`(int.star-contains (lambda ((x1 Int) ...) (and (= z1 (ite ...)) ...))
k1 k2 1 0 0)` — well before any lia* lemma was sent.

### Root cause

`STAR_CONTAINS` is registered as a closure kind in
[`src/expr/kind_template.cpp:76`](src/expr/kind_template.cpp#L76)
(by commit `6695617930` "isClosure(STAR_CONTAINS) = true;"), so that
term-registration and other closure-aware passes treat it like a
binder. **But unlike true binders (`FORALL` / `EXISTS` / `LAMBDA` / …)
its first child is a `LAMBDA`, not a `BOUND_VAR_LIST`.**

Two pieces of generic proof machinery assumed `cur[0]` of every closure
is an immutable bound-variable list:

1. **`TConvProofGenerator::getProofForRewriting`** in
   [`src/proof/conv_proof_generator.cpp`](src/proof/conv_proof_generator.cpp)
   asserts `cur[0] == ret[0]` and uses `startIndex = 1` to skip the
   first child as a congruence premise. When the rewriter normalised
   arithmetic / removed `(- L x)` etc. inside the embedded lambda's
   body, the lambda itself changed → `cur[0] != ret[0]` →
   assertion failure.

2. **`UfProofRuleChecker::checkInternal`** in
   [`src/theory/uf/proof_checker.cpp`](src/theory/uf/proof_checker.cpp)
   auto-injects `t[0]` into both `lchildren` and `rchildren` for any
   closure. With `STAR_CONTAINS` this prepended the lambda to the
   reconstructed term, so `CONG` produced a 7-arg
   `(int.star-contains lambda lambda k1 k2 1 0 0)` instead of the
   expected 6-arg `(int.star-contains new-lambda k1 k2 1 0 0)`.

### Fix

In both places, narrow the closure-special-casing to
`cur.isClosure() && cur[0].getKind() == Kind::BOUND_VAR_LIST` so that
true binders still take the binder path while `STAR_CONTAINS`
(and any future "closure for term-registration only" kind) falls
through to the regular `CONG` path.

```cpp
// src/proof/conv_proof_generator.cpp
if (cur.isClosure() && cur[0].getKind() == Kind::BOUND_VAR_LIST)
{
  startIndex = 1;
  Assert(cur[0] == ret[0]);
}

// src/theory/uf/proof_checker.cpp
if (t.isClosure() && t[0].getKind() == Kind::BOUND_VAR_LIST)
{
  lchildren.push_back(t[0]);
  rchildren.push_back(t[0]);
}
```

`STAR_CONTAINS` remains a closure kind in `kind_template.cpp` because
`term_registration_visitor.cpp:91` and other places rely on that bit
to skip term registration of the bound-variable subterms.

---

## Part 2 — Lazy proof generator for lia* lemmas

Three lemmas are emitted by `LiaStarExtension::checkFullEffort`
([`src/theory/arith/liastar/liastar_extension.cpp`](src/theory/arith/liastar/liastar_extension.cpp)):

| Lemma | Form | Proof rule |
|---|---|---|
| split        | `vp ∨ ¬vp`, where `vp = predicate[v_1, ..., v_n]` | `ProofRule::SPLIT` |
| non-negativity | `(>= v_1 0) ∧ ... ∧ (>= v_n 0)`           | `TRUST` w/ `ARITH_LIA_STAR_NONNEGATIVE` |
| reduction    | `(int.star-contains lambda v) = star`           | `TRUST` w/ `ARITH_LIA_STAR_CONTAINS_REDUCE` |

The two `TRUST` rules are placeholders. Each is the seam where a
subsolver-derived proof can later replace the trust step (path "(b)"
in `proof_pipeline_notes.md` §6 / §9 step 6: instantiate a fresh
`SolverEngine`, run it on the lemma, transcribe the resulting
`ProofNode` onto the parent `ProofNodeManager`, return that instead).

### New TrustIds

[`src/proof/trust_id.h`](src/proof/trust_id.h) and
[`src/proof/trust_id.cpp`](src/proof/trust_id.cpp) gain two entries
under the arith block:

```cpp
ARITH_LIA_STAR_NONNEGATIVE,
ARITH_LIA_STAR_CONTAINS_REDUCE,
```

### `LiaStarProofGenerator`

New files
[`src/theory/arith/liastar/liastar_proof_generator.h`](src/theory/arith/liastar/liastar_proof_generator.h)
and
[`src/theory/arith/liastar/liastar_proof_generator.cpp`](src/theory/arith/liastar/liastar_proof_generator.cpp).

```cpp
class LiaStarProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  LiaStarProofGenerator(Env& env, context::Context* c);

  void registerSplit(Node lemma, Node vectorPredicate);
  void registerNonnegative(Node lemma, Node literal);
  void registerContainsReduce(Node lemma, Node literal, Node star);

  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  bool hasProofFor(Node fact) override;
  std::string identify() const override;

 private:
  enum class Kind : uint32_t { SPLIT, NONNEGATIVE, CONTAINS_REDUCE };
  struct Info { Kind d_kind; Node d_aux; };

  std::shared_ptr<ProofNode> mkSplitProof(Node, const Info&);
  std::shared_ptr<ProofNode> mkNonnegativeProof(Node, const Info&);
  std::shared_ptr<ProofNode> mkContainsReduceProof(Node, const Info&);

  context::CDHashMap<Node, uint32_t> d_kind;
  context::CDHashMap<Node, Node> d_aux;
};
```

Two design choices:

1. **Lazy.** `register*` only stores per-fact metadata (kind + the
   originating literal / vector predicate) in user-context-dependent
   maps. The actual `ProofNode` is built only when `getProofFor(fact)`
   is invoked at proof-finalisation time.
2. **One generator, three rules.** All three lemma kinds share a
   single `LiaStarProofGenerator` instance and a single
   `(d_kind, d_aux)` map pair. `getProofFor` dispatches on the
   recorded `Kind`. Adding a fourth lemma is a matter of adding
   an enum entry and an `mk...Proof` method.

### Wiring

In [`liastar_extension.h`](src/theory/arith/liastar/liastar_extension.h):

```cpp
std::unique_ptr<LiaStarProofGenerator> d_proofGen;
```

In [`liastar_extension.cpp`](src/theory/arith/liastar/liastar_extension.cpp),
construction guarded on `env.isTheoryProofProducing()`:

```cpp
if (env.isTheoryProofProducing())
{
  d_proof.reset(new CDProofSet<CDProof>(env, env.getUserContext(), "liastar-ext"));
  d_proofGen.reset(new LiaStarProofGenerator(env, env.getUserContext()));
}
```

Each `addPendingLemma` call now first registers the lemma with
`d_proofGen` and passes the generator pointer:

```cpp
if (d_proofGen != nullptr) d_proofGen->registerNonnegative(nonnegative, literal);
d_im.addPendingLemma(nonnegative,
                     InferenceId::ARITH_LIA_STAR_NONNEGATIVE,
                     d_proofGen.get());

Node split = vectorPredicate.orNode(vectorPredicate.notNode());
if (d_proofGen != nullptr) d_proofGen->registerSplit(split, vectorPredicate);
d_im.addPendingLemma(split, InferenceId::ARITH_LIA_STAR_SPLIT, d_proofGen.get());

Node lemma = literal.eqNode(star);
if (d_proofGen != nullptr) d_proofGen->registerContainsReduce(lemma, literal, star);
d_im.addPendingLemma(lemma, InferenceId::ARITH_LIA_STAR_EXISTS, d_proofGen.get());
```

### Build

[`src/CMakeLists.txt`](src/CMakeLists.txt) gains the two new source
files in the lia* block.

---

## Files touched

| File | Change |
|---|---|
| `src/proof/conv_proof_generator.cpp` | narrow closure check |
| `src/theory/uf/proof_checker.cpp`    | narrow closure check |
| `src/proof/trust_id.h`               | add 2 TrustIds |
| `src/proof/trust_id.cpp`             | add 2 toString cases |
| `src/theory/arith/liastar/liastar_extension.h`  | declare `d_proofGen`, include header |
| `src/theory/arith/liastar/liastar_extension.cpp`| allocate generator, register + pass pg in `addPendingLemma` |
| `src/theory/arith/liastar/liastar_proof_generator.h`   | new — generator declaration |
| `src/theory/arith/liastar/liastar_proof_generator.cpp` | new — generator implementation; non-negativity uses originating literal as TRUST premise |
| `src/CMakeLists.txt`                  | add new files |
| `src/proof/eo/eo_print_channel.cpp`   | per-TrustId rule-name dispatch in `printTrustStep` |
| `proofs/eo/cpc/expert/rules/ArithLiaStar.eo` | new — Eunoia rule declarations for the lia* trust IDs |
| `proofs/eo/cpc/expert/CpcExpert.eo`   | include the new lia* signatures |
| `test/regress/cli/regress1/arith/liastar/paper2008.smt2` | drop `; DISABLE-TESTER: proof` |

---

## Verification

```
$ build/bin/cvc5 --check-proofs --proof-check=lazy \
      test/regress/cli/regress1/arith/liastar/paper2008.smt2
unsat
```

All other lia* regressions (`disjoint_union`, `f2_sat`, `f2_unsat`,
`paper2020`, `sat1`, `sat2`, `simple`) match their declared `:status`
under `--check-proofs --proof-check=lazy`. (`query026` times out at
60s, independent of these changes.)

Spot-checked quantifier regressions (`006-cbqi-ite`, `015-psyco-pp`,
`AdditiveMethods_OwnedResults.Mz`, …) under
`--check-proofs --proof-check=lazy` to confirm the closure-check
narrowing did not regress true binders.

---

## Part 3 — CPC printer + Eunoia signatures

### Symptom

Running `--produce-proofs --proof-format-mode=cpc --dump-proofs` on a
benchmark that hit `LiaStarProofGenerator` produced

```
; WARNING: add trust step for TRUST
; trust TRUST ARITH_LIA_STAR_CONTAINS_REDUCE
(step @pXX <conclusion> :rule trust :premises () :args (...))
```

The warning is emitted at
[`src/proof/eo/eo_print_channel.cpp`](src/proof/eo/eo_print_channel.cpp)
once per `ProofRule` (`TRUST`) whenever any `TRUST` step is printed.
Even with TrustId-specific Eunoia signatures the warning would persist,
because the printer hardcoded `:rule trust` for every `TRUST` step.

### Fix

Two coordinated changes:

1. **Per-TrustId rule-name dispatch in the printer.** Add
   `trustIdRuleName(TrustId)` returning `"arith_lia_star_nonnegative"`,
   `"arith_lia_star_contains_reduce"`, or empty for unknown IDs. In
   `printTrustStep`, when the trust step has a registered TrustId,
   emit it via `printStepInternal(rname, ...)` (mirroring the shape of
   the catch-all `trust` rule: premises preserved, single `:args`
   carrying the conclusion) and skip both the `; WARNING` and the
   `; trust ...` comment. Unknown TrustIds still go through the
   generic catch-all path with the warning intact.

2. **Eunoia signatures.** A new file
   [`proofs/eo/cpc/expert/rules/ArithLiaStar.eo`](proofs/eo/cpc/expert/rules/ArithLiaStar.eo)
   declares two `:sorry` axiom rules
   (`arith_lia_star_nonnegative`, `arith_lia_star_contains_reduce`),
   shape-matched to the catch-all `trust` rule (premise list of Bool
   formulas, one Bool argument naming the conclusion). These are
   wired into the expert signature index via
   [`proofs/eo/cpc/expert/CpcExpert.eo`](proofs/eo/cpc/expert/CpcExpert.eo).
   Like the generic `trust` rule they keep the proof "incomplete"
   until the lia*-derived discharge is implemented, but the external
   eo checker can now refer to them by their specific names.

After these:

```
$ build/bin/cvc5 --produce-proofs --check-proofs --proof-check=lazy \
      --proof-format-mode=cpc --dump-proofs paper2008.smt2 \
      | grep -E 'WARNING|^; trust'
$ # (no output)
$ build/bin/cvc5 ... --dump-proofs paper2008.smt2 | grep arith_lia_star
(step @pXX :rule arith_lia_star_contains_reduce :premises () :args (...))
```

### Improvement to the non-negativity TRUST step

`LiaStarProofGenerator::mkNonnegativeProof` now passes the originating
`STAR_CONTAINS` literal as a premise to the `addTrustedStep` call:

```cpp
cdp.addTrustedStep(
    lemma, TrustId::ARITH_LIA_STAR_NONNEGATIVE, {info.d_aux}, {});
```

The proof shape becomes
`STAR_CONTAINS(lambda, v) ⊢ (>= v_1 0) ∧ ... ∧ (>= v_n 0)` rather
than an unconditional axiom — structurally aligning the trust step
with what a real proof (subsolver-derived or otherwise) would look
like.

The reduction lemma `(int.star-contains lambda v) = star` has no
analogous premise: it is a tautology of the lia* algorithm itself.
The TRUST step there carries no premise.

---

## Part 4 — On filling the `:sorry` (analysis, not implemented)

After Part 3 the proof file is clean of the `; WARNING` line and the
two trust steps print under the lia*-specific Eunoia rule names — but
those rules are still `:sorry` axioms in
[`proofs/eo/cpc/expert/rules/ArithLiaStar.eo`](proofs/eo/cpc/expert/rules/ArithLiaStar.eo).
The natural follow-up is "drop the `:sorry`". This section records why
that's not a quick mechanical step.

### Why neither rule has an obvious fill

**`arith_lia_star_contains_reduce`** — its conclusion is
`(int.star-contains L v_1 ... v_n) = star`, where `star` is the
Hilbert-basis cone decomposition produced at runtime by `libnormaliz`
(`LiaStarExtension::getCones`). Filling this `:sorry` non-trivially
means re-implementing the lia* algorithm (cone construction over
integer polyhedra, Hilbert basis, module generators) inside Eunoia so
the eo checker can reproduce the equality. That's reproducing
libnormaliz in `eo` — substantive, not syntactic.

**`arith_lia_star_nonnegative`** — semantically simpler (the
non-negativity of the argument vector is a definitional property of
lia*) but still requires *defining* `int.star-contains`'s semantics in
Eunoia. cvc5 doesn't currently declare `int.star-contains` in any
`.eo` file; the operator is unknown to the eo checker. A real fill
would need:

1. `(declare-parameterized-const int.star-contains …)` with a workable
   encoding for "lambda followed by variadic ints". Eunoia's
   `:right-assoc-nil` only handles a homogeneous variadic tail, and
   the lambda first-arg breaks that pattern, so this needs a custom
   wrapper or a new kind.
2. A semantic definition of `int.star-contains` (an existential over
   non-negative coefficients and witness vectors) as a recursive
   Eunoia program.
3. A derivation that pattern-matches the variadic args of the premise
   and produces the matching conjunction of `(>= v_i 0)`.

That's a non-trivial Eunoia engineering project.

### Cheaper-but-incomplete improvements that *are* feasible

Without the full formalization, the rule could still be tightened with
a structural shape check via `:requires` — verify the conclusion is a
conjunction of `(>= v_i 0)` whose `v_i`s match the integer args of the
premise's `int.star-contains`. That tightens "what shape of conclusion
this rule will accept" but doesn't *prove* the conclusion semantically;
the rule would still need `:sorry` because the eo checker has no
semantics for `int.star-contains` to derive from. Worth doing as
defense-in-depth, but not done here.

### Recommended path forward (in order of difficulty)

1. Add a `:requires` shape check to `arith_lia_star_nonnegative`
   (small, real, still `:sorry`, catches misuse).
2. Declare `int.star-contains` and add a recursive Eunoia program that
   models its semantics; drop `:sorry` from
   `arith_lia_star_nonnegative` (medium-sized, needs experiment with
   the eo checker).
3. Replace the `mkContainsReduceProof` body with a real proof —
   either subsolver-derived (sketch below) or by formalizing the
   Hilbert-basis decomposition in Eunoia (large).

### Subsolver-derived proof sketch (for option 3)

```cpp
// in liastar_proof_generator.cpp
std::shared_ptr<ProofNode> LiaStarProofGenerator::mkContainsReduceProof(
    Node lemma, const Info& info)
{
  // 1. Spawn a subsolver and ask it to refute ¬lemma.
  std::unique_ptr<SolverEngine> sub;
  initializeSubsolver(sub, d_env);
  sub->assertFormula(lemma.notNode());
  Result r = sub->checkSat();
  Assert(r.isUnsat());

  // 2. Pull its FULL proof and transcribe onto our PNM.
  auto pfs = sub->getProof(modes::ProofComponent::FULL);
  // ... transcribe pfs[0] (rooted at SCOPE([¬lemma]) ⊢ ⊥) into a
  //     ProofNode concluding `lemma`, allocated via
  //     d_env.getProofNodeManager().

  // 3. Return that instead of the TRUST step.
  return /* transcribed proof of `lemma` */;
}
```

Caveat: a generic subsolver doesn't natively handle `int.star-contains`
(the operator only lives inside the lia* extension), so the subsolver
would need to also be running lia*. This is circular for the
*reduction* lemma (which is the algorithm itself). The non-negativity
lemma is more amenable: with the originating `STAR_CONTAINS` literal
asserted as a premise, a lia*-aware subsolver can derive the
non-negativity conjunction directly.

### Status

The placeholders remain. The infrastructure (TrustIds, generator,
printer dispatch, named Eunoia rules, premise wiring on the
non-negativity step) is set up so that when any of options (1)/(2)/(3)
above is implemented, the change is local to either
`liastar_proof_generator.cpp` or
`proofs/eo/cpc/expert/rules/ArithLiaStar.eo` and does not touch the
generic proof machinery.
