; EXPECT: sat
(set-logic ALL)
(set-option :sets-ext true)
(set-option :produce-unsat-cores true)
(assert (set.choose (set.insert (set.is_singleton (set.complement (set.singleton true))) (set.complement (set.complement (set.singleton true))))))
(check-sat)
