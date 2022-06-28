; COMMAND-LINE: --deep-restart=input
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
(set-logic ALL)
(declare-const v (_ BitVec 2))
(declare-const x7 Bool)
(declare-const x Bool)
(declare-const x79 Bool)
(declare-const x799 (_ BitVec 1))
(check-sat-assuming ((and (distinct (_ bv0 1) (ite x (_ bv1 1) (_ bv0 1))) (or (bvsge (_ bv0 1) (ite x7 (_ bv1 1) (_ bv0 1))) x7) (not (= (_ bv0 4) ((_ zero_extend 3) (ite x79 (_ bv1 1) (_ bv0 1))))) (or x79 (distinct (_ bv0 4) (bvxor (_ bv2 4) ((_ zero_extend 3) (ite x79 (_ bv1 1) (_ bv0 1)))))) (bvuge (_ bv1 4) ((_ sign_extend 1) ((_ repeat 3) (ite (= (_ bv0 4) ((_ sign_extend 3) (ite (distinct (_ bv0 4) (bvor (_ bv1 4) ((_ zero_extend 2) v))) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1))))) (bvsgt (_ bv0 4) ((_ repeat 4) (ite (bvslt (ite (distinct (_ bv0 4) ((_ sign_extend 3) (ite (bvslt (_ bv0 1) x799) (_ bv1 1) (_ bv0 1)))) (_ bv1 1) (_ bv0 1)) (_ bv0 1)) (_ bv1 1) (_ bv0 1)))))))
