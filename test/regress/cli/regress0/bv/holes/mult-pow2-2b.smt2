; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const z (_ BitVec 4))
(assert (not (=
  (bvmul z #b1100)
  (concat
    ((_ extract 1 0) (bvneg z))
    #b00)
	)))
(check-sat)
(exit)
