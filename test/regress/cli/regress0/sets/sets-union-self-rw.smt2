; EXPECT: unsat
; Regression for the sets-union-self rewrite, which proves (set.union s s) = s.
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (or (not (= (set.union s s) s))
            (not (= (set.union (set.minus s t) (set.minus s t)) (set.minus s t)))))
(check-sat)
