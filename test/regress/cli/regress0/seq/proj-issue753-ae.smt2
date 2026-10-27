; EXPECT: unsat
(set-logic ALL)
(check-sat-assuming ((seq.prefixof (seq.++ (seq.unit false) (seq.unit false)) (seq.unit false))))
