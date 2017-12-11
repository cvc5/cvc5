; COMMAND-LINE: --cbqi-bv
; EXPECT: unsat
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun c () (_ BitVec 1))

(assert (forall ((x (_ BitVec 32))) (not (= (bvcomp x a) (bvcomp x b)))))

(check-sat)
