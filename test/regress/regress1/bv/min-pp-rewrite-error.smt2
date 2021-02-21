(set-logic QF_BV)
(set-info :status unsat)
(declare-fun v2 () (_ BitVec 4))
(check-sat-assuming ((and (not (= (_ bv1 4) ((_ sign_extend 3) (ite (bvsgt v2 (_ bv0 4)) (_ bv1 1) (_ bv0 1))))) (bvsge (_ bv1 1) (bvnand (_ bv1 1) (ite (= (_ bv1 4) ((_ sign_extend 3) (ite (bvslt v2 (_ bv0 4)) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)))) (bvsgt (_ bv0 4) ((_ sign_extend 3) (ite (bvsle (_ bv0 1) (ite (bvsle (_ bv1 1) (ite (bvugt (_ bv1 4) ((_ sign_extend 3) (ite (bvuge v2 (_ bv1 4)) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)))))))
