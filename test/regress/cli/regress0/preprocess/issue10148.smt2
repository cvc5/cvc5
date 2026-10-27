; EXPECT: unsat
(set-logic ALL)
(declare-const x Int)
(declare-fun v () String)
(assert (and (> 0 x) (distinct 0 (ite (= "\n" (str.at v 0)) 1 0))))
(check-sat)
