; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (not (=
	(bvmul (bvadd x y) #b0100)
	(bvadd (bvmul x #b0100) (bvmul y #b0100)))))
(check-sat)
(exit)
