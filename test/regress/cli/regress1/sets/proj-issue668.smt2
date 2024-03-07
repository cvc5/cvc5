; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(set-option :sat-solver cadical)
(set-option :incremental true)
(declare-sort u 0)
(declare-const x u)
(assert (seq.nth (seq.unit (set.is_singleton (set.minus (set.singleton (_ bv0 67)) (set.singleton (_ bv0 67))))) (set.card (set.singleton x))))
(check-sat-assuming ((seq.nth (seq.unit (set.is_singleton (set.singleton (_ bv0 67)))) (set.card (set.singleton x)))))
(check-sat)
