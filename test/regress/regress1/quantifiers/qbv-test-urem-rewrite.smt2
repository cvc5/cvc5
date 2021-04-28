; COMMAND-LINE: --cegqi-bv --cegqi-bv-ineq=keep --no-cegqi-full
; EXPECT: sat
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))

(assert (forall ((x (_ BitVec 4))) (not (= (bvurem x a) b))))

(check-sat)
