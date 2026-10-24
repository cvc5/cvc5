# Building cvc5 for local-search base implementation
- Change to the ls-base branch
```
./configure.sh debug --auto-download --ninja
cd build && ninja -j$(nproc)
```

```
ctest -R bv -j$(nproc)
./bib/cvc5 --version
```

# Understanding the bit-blasting mechanism

## The default mechanism
- cvc5 by default uses `BVSolverBitblas::postCheck` for `QF_BV`.

## Some important program points
```
grep -n "postCheck\|preNotifyFact\|d_satSolver\|solve(" src/theory/bv/bv_solver_bitblast.cpp | head -40
```

## Decision
`147:void BVSolverBitblast::postCheck(Theory::Effort level)`
- Definition of `postCheck`. 
- This is the method wich cvc5 calls when it needs to decide. Bit-blasting facts and calls sat.
- Verify the theory consistence.

`152:    if (!d_propagate || !d_satSolver->setPropagateOnly())`
- If the level of effort is not FULL, then just make the bit propagation.

`162:    d_satSolver.reset(nullptr);`
- Recreate the sat-solver after a reset.
- **Observation.** Line 171 process a queue of bit-blasting facts.

## SAT solver call
`227:  prop::SatValue val = d_satSolver->solve(assumptions);`
- The SAT solver call.
- `d_satSolver->solve(assumptions)` is the SAT call inside `postCheck`. Probably, the ternary-local search will be implemented before it, when `level == Theory::EFFORT_FULL`.
If ternary local-search finds a model, then return sat status without calls the sat.

242:    d_satSolver->getUnsatAssumptions(unsat_assumptions);
- `getUnsatAssumptions`, if unsat, build the conflict. It can be useful for the **research question**, I think.

## Atoms and model
276:bool BVSolverBitblast::preNotifyFact(CVC5_UNUSED TNode atom,
- One bv was asserted.
- `preNotifyFact` is where the facts, atoms, arrive and are stored.

355:      prop::SatValue value = d_satSolver->modelValue(bit);
- modelValue, it can be a reference for how to make our own model.

372:  d_satSolver.reset(factory(d_env,
- idk
378:                                        d_satSolver.get(),
- idk
411:      prop::SatValue val = d_satSolver->modelValue(lit);
- modelValue again
- idk

500:    result = d_satSolver->solve(assumptions);
- I didn't understanding well. Why is it calling solve again?


//////////////////////////////////////////////////////////////////////////////////////////////////


# Project decisions
- It will be important to have an option "--tls" for example, to enable the ternary local-search.
- Probably line 227 is important, we probably want to implement the ternary local-search **before** it.
