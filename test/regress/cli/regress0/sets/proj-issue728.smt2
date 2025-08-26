; EXPECT: sat
(set-logic ALL)
(set-option :sets-exp true)
(set-option :debug-check-models true)
(assert (set.is_singleton (set.complement (set.singleton roundTowardZero))))
(check-sat)
