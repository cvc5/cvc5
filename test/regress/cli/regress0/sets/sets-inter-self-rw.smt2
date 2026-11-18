; EXPECT: unsat
; Regression for the sets-inter-self rewrite, which proves (set.inter s s) = s.
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (or (not (= (set.inter s s) s))
            (not (= (set.inter (set.minus s t) (set.minus s t)) (set.minus s t)))))
(check-sat)
