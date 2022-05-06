; DISABLE-TESTER: lfsc
; COMMAND-LINE: --cegqi-bv --cegqi-bv-ineq=keep --no-cegqi-full
; EXPECT: unsat
(set-logic BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 1))

(assert (forall ((x (_ BitVec 8))) (not (= (bvcomp x a) ((_ extract 7 7) (bvmul a b))))))

(check-sat)
