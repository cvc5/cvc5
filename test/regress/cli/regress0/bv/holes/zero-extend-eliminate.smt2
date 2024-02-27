; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(assert (not (=
	((_ zero_extend 5) x)
	(concat #b00000 x)
	)))
(check-sat)
(exit)
