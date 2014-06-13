(set-logic QF_BV)
(set-info :status sat)
(declare-fun v0 () (_ BitVec 2))
(assert
	(xor
		(bvslt (_ bv0 5)
		       (bvlshr (bvadd (_ bv5 5) ((_ sign_extend 3) v0)) ((_ sign_extend 3) v0)))
	     	 (bvult (_ bv5 5)
	     	        (bvlshr (bvadd (_ bv5 5) ((_ sign_extend 3) v0)) ((_ sign_extend 3) v0)))))
(check-sat)

