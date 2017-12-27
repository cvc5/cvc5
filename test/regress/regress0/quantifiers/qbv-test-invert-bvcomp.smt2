; COMMAND-LINE: --cbqi-bv --cbqi-bv-ineq=keep --no-cbqi-full
; EXPECT: unsat
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 1))

(assert (forall ((x (_ BitVec 8))) (not (= (bvcomp x a) ((_ extract 7 7) (bvmul a b))))))

(check-sat)
