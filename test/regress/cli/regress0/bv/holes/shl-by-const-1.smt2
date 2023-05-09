; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 10))
(assert (not (=
	(bvshl x #b0000000101)
	(concat ((_ extract 4 0) x) #b00000)
	)))
(check-sat)
(exit)
