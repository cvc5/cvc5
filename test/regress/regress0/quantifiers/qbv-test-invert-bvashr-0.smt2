; COMMAND-LINE: --cbqi-bv
; EXPECT: sat
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))

(assert (forall ((x (_ BitVec 32))) (not (= (bvashr x a) b))))

(check-sat)
