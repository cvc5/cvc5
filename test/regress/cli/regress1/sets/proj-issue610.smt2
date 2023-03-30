; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-option :sets-ext true)
(declare-const x (Set (Array Bool Bool)))
(assert (select (set.choose (set.minus (set.singleton (set.choose (set.complement x))) (set.minus (set.singleton (set.choose (set.complement x))) (set.minus (set.singleton (set.choose (set.complement x))) (set.minus (set.singleton (set.choose (set.complement x))) (set.minus (set.singleton (set.choose (set.complement x))) x)))))) (seq.prefixof seq.empty seq.empty)))
(assert (select (set.choose (set.minus (set.singleton (set.choose (set.complement x))) (ite (select (set.choose x) false) x (set.complement x)))) (seq.prefixof seq.empty seq.empty)))
(check-sat)
