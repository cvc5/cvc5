; EXPECT: unsat
(set-logic ALL)
(declare-const t (_ BitVec 1))
(assert (distinct (= (_ bv0 4) ((_ zero_extend 3) t)) (exists ((x (_ BitVec 4))) (= ((_ sign_extend 4) x) (concat ((_ zero_extend 3) t) (_ bv0 4))))))
(check-sat)
