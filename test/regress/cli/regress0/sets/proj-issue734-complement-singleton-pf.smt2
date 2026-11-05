; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(set-option :check-unsat-cores true)
(set-option :sets-exp true)
(set-option :mbqi-enum true)
(set-option :sets-proxy-lemmas true)
(declare-sort u 0)
(declare-const x u)
(assert (not (set.is_singleton (set.complement (set.singleton x)))))
(check-sat)
