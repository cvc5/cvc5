; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3
; EXPECT: sat
; A satisfiable multiplication (a * b = 15 with a, b > 1) whose initial
; over-approximation is spurious: the refinement loop must add lemmas and
; re-solve before returning a model consistent with the abstracted bvmul.
(set-logic QF_BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(assert (= (bvmul a b) (_ bv15 16)))
(assert (bvugt a (_ bv1 16)))
(assert (bvugt b (_ bv1 16)))
(check-sat)
