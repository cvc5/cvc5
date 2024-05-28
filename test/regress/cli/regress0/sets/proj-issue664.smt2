; EXPECT: sat
(set-logic ALL)
(set-option :sets-ext true)
(set-option :produce-interpolants true)
(check-sat-assuming ((bag.subbag (bag (set.singleton (as set.universe (Set String))) (set.card (as set.universe (Set String)))) (bag (set.complement (set.complement (set.complement (set.singleton (as set.universe (Set String)))))) (set.card (as set.universe (Set String)))))))
