; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(declare-const y (_ BitVec 5))
(assert (and (bvsgt x #b00000) (bvsgt y #b00000) (not (=
	(bvsrem x y)
  (ite (bvuge x #b10000) (bvneg (bvurem x y)) (bvurem x y))))))
(check-sat)
(exit)
