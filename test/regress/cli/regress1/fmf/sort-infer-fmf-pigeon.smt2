; Sort inference + FMF soundness regression test.
; Sort inference splits U into subsorts and marks some monotonic. FMF only bounds
; non-monotonic subsorts, leaving monotonic subsorts unbounded. This breaks the
; cardinality constraints imposed by the injections sort inference adds between
; subsorts, allowing FMF to find spurious models on UNSAT problems.
; The fix: sort inference is disabled when --finite-model-find is active.
; COMMAND-LINE: --finite-model-find --sort-inference
; EXPECT: unsat
(set-logic UF)
(set-info :status unsat)
(declare-sort U 0)
; Bound U to 2 elements
(declare-const e1 U)
(declare-const e2 U)
(assert (not (= e1 e2)))
(assert (forall ((x U)) (or (= x e1) (= x e2))))
; Pigeonhole: injective f: U -> U with constant c not in range of f
(declare-fun f (U) U)
(declare-const c U)
(assert (forall ((X U)) (not (= (f X) c))))
(assert (forall ((X U) (Y U)) (=> (= (f X) (f Y)) (= X Y))))
(check-sat)
