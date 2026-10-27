; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 10))
(assert (not (=
	((_ repeat 5) x)
	(concat x ((_ repeat 4) x))
	)))
(check-sat)
(exit)
