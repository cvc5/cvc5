; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3
; EXPECT: sat
; Satisfiable variant of the QF_ABV abstraction tests: the abstracted bvmul
; both takes a select in its operand and feeds a select index. Checks that the
; refinement converges to a model consistent across BV and arrays (the model
; configuration of the regression runner re-checks the model).
(set-logic QF_ABV)
(declare-fun arr () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun x () (_ BitVec 8))
(assert (= (bvmul (select arr x) (_ bv3 8)) (_ bv30 8)))
(assert (= (select arr (bvmul x (select arr x))) (_ bv7 8)))
(check-sat)
