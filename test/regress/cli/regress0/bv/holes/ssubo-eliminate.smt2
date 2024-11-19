; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

; This should be unsat but it is sat. What is going on here?
(declare-const x (_ BitVec 5))
(declare-const y (_ BitVec 5))
(assert (not (=
	(bvssubo x y)
	(or
		(and
			(= ((_ extract 4 4) x) #b1) ; x < 0
			(not (= ((_ extract 4 4) y) #b1)) ; !(y < 0)
			(not (= ((_ extract 4 4) (bvsub x y)) #b1)) ; !(s < 0)
		)
		(and
			(not (= ((_ extract 4 4) x) #b1)) ; !(x < 0)
			(= ((_ extract 4 4) y) #b1) ; y < 0
			(= ((_ extract 4 4) (bvsub x y)) #b1) ; s < 0
		)
	))))
(check-sat)
(exit)
