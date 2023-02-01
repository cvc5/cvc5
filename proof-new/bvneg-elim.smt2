(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-fun x0 () (_ BitVec 8))
(assert (not (= (bvneg (bvneg x0)) x0)))
(check-sat)
(exit)
