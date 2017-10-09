; COMMAND-LINE: --cbqi-bv
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 32))

(assert (forall ((x (_ BitVec 32))) (not (bvult x a) )))

(check-sat)
