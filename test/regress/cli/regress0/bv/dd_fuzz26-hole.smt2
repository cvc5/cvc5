; EXPECT: unsat
(set-logic ALL)
(declare-const v (_ BitVec 1))
(check-sat-assuming ((not (bvuge (bvnor (bvor (_ bv2 4) (_ bv1 4)) (bvlshr ((_ zero_extend 3) v) (_ bv0 4))) (_ bv1 4)))))
