; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 10))
(assert (not (=
	(bvslt x #b0000000000)
	(= ((_ extract 9 9) x) #b1)
	)))
(check-sat)
(exit)
