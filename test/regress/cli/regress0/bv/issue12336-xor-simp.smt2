; EXPECT: unsat
(set-logic QF_BV)
(declare-const r (_ BitVec 1))
(assert (= (_ bv0 8) ((_ extract 15 8) (concat (bvxor ((_ zero_extend 7) r) (bvnot ((_ zero_extend 7) r))) (_ bv0 8)))))
(check-sat)
