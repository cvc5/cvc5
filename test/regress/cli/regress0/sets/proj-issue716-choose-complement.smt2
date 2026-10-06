; REQUIRES: unrestricted-mode
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(set-option :sets-exp true)
(set-option :incremental true)
(set-option :sat-solver cadical)
(assert (not (set.choose (set.minus (set.complement (set.singleton true)) (set.choose (set.singleton (set.complement (set.minus (set.singleton true) (set.singleton true)))))))))
(check-sat-assuming (true))
(check-sat)
