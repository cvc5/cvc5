; EXPECT: unsat
(set-logic ALL)
(declare-const x (_ BitVec 1))
(check-sat-assuming ((bvult (_ bv1 3) (bvmul ((_ sign_extend 2) x) ((_ repeat 3) (_ bv1 1))))))
