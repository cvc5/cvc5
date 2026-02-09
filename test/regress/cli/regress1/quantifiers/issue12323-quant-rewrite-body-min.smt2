; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(declare-const t String)
(assert (forall ((i Int)) (and (not x) (or (distinct "" (ite (= i 0) "" t)) (distinct "" (ite x t (ite (= i 0) "" t)))))))
(check-sat)
