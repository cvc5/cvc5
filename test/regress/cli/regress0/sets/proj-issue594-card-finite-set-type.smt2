; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(set-option :sets-exp true)
(declare-const x (Set (Set Bool)))
(declare-const x6 Bool)
(assert (> (set.card x) (ite (ite (set.is_singleton x) (set.is_singleton x) x6) 0 (set.card x))))
(check-sat-assuming (((_ divisible 5) (* (set.card x) (ite (set.is_singleton x) 1 (set.card x))))))
