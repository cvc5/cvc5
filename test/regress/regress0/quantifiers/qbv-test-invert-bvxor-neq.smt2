; COMMAND-LINE: --cegqi-bv --cegqi-bv-ineq=keep --no-cegqi-full
; EXPECT: unsat
(set-logic BV)
(set-info :status unsat)
(declare-fun a () (_ BitVec 8))

(assert (forall ((x (_ BitVec 8))) (not (= (bvxor x a) (bvmul a a)))))

(check-sat)
