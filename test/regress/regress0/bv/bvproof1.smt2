(set-logic QF_BV)
(set-info :status unsat)
(declare-const x Bool)
(check-sat-assuming ((not (bvuge (bvcomp (_ bv0 4) (_ bv0 4)) (ite x (_ bv1 1) (_ bv0 1))))))
