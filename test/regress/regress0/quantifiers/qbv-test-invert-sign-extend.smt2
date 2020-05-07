; COMMAND-LINE: --cegqi-bv --cegqi-bv-ineq=keep --no-cegqi-full
; EXPECT: sat
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 16))

(assert (forall ((x (_ BitVec 8))) (not (= ((_ sign_extend 8) x) b))))

(check-sat)
