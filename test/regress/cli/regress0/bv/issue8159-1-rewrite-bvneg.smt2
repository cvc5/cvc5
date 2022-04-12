; COMMAND-LINE: --incremental
(set-logic QF_BV)
(assert (= (_ bv1 1) (bvsmod (_ bv0 1) (bvneg (bvneg (_ bv0 1))))))
(push)
(set-info :status unsat)
(check-sat)
