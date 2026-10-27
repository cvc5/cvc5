; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(declare-const y (_ BitVec 5))
(declare-const z (_ BitVec 5))
(assert (not (=
	(bvneg (bvadd x y z))
	(bvadd (bvneg x) (bvneg y) (bvneg z)))))
(check-sat)
(exit)
