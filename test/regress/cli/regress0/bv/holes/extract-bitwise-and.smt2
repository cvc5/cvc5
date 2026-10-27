; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(declare-const y (_ BitVec 5))
(assert (not (=
	((_ extract 4 3) (bvand x y))
	(bvand ((_ extract 4 3) x) ((_ extract 4 3) y))
	)))
(check-sat)
(exit)
