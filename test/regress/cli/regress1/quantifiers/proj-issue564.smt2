; EXPECT: unsat
; DISABLE-TESTER: lfsc
(set-logic ALL)
(set-option :sets-ext true)
(set-option :ieval use-learn)
(check-sat-assuming ((set.is_singleton (set.comprehension ((_x0 Real)) false 0.0))))
