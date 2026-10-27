; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x1 (_ BitVec 10))
(declare-const x2 (_ BitVec 10))
(declare-const x3 (_ BitVec 10))
(declare-const x4 (_ BitVec 10))
(declare-const y (_ BitVec 10))
(assert (not (=
	((_ extract 25 15) (concat x3 x2 x1 x4))
	(concat ((_ extract 5 0) x2) ((_ extract 9 5) x1)))))
(check-sat)
(exit)
