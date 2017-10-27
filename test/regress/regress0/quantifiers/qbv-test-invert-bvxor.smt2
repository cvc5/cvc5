; COMMAND-LINE: --cbqi-bv
; EXPECT: unsat
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 32))

(assert (forall ((x (_ BitVec 32))) (not (= (bvxor x a) (bvmul a a)))))

(check-sat)
