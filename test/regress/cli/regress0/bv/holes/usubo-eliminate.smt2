; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

; This should be unsat but it is sat. What is going on here?
(declare-const x (_ BitVec 5))
(declare-const y (_ BitVec 5))
(assert (not (=
	(bvusubo x y)
  (= ((_ extract 5 5) (bvsub ((_ zero_extend 1) x) ((_ zero_extend 1) y))) #b1))))
(check-sat)
(exit)
