; EXPECT: unsat
(set-logic ALL)
(declare-fun v () String)
(assert (distinct 0 (ite (str.contains (str.substr (str.substr v 0 1) 0 (str.indexof (str.substr v 0 1) "," 0)) "G") 1 0)))
(check-sat)
