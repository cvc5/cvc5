(set-logic QF_BV)
(assert (bvsle (concat (_ bv1 1) (_ bv0 1) ((_ zero_extend 1) (_ bv0 1))) (concat (_ bv1 1) ((_ zero_extend 1) (_ bv0 1)) (bvnot (bvnot (bvnot (_ bv0 1)))))))
(set-info :status sat)
(check-sat)
