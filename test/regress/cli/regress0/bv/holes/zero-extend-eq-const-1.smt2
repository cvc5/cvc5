; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 3))
(assert (not (=
	(= ((_ zero_extend 3) x) #b000111)
	(and
		(= ((_ extract 5 3) #b000111) #b000)
		(= x ((_ extract 2 0) #b000111))
	))))
(check-sat)
(exit)
