; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 4))
(assert (not (=
	(bvmul (bvneg x) #b0100)
	(bvmul x #b1100))))
(check-sat)
(exit)
