; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 4))
(assert (not (=
	((_ repeat 3) x)
	(concat x ((_ repeat 2) x))
	)))
(check-sat)
(exit)
