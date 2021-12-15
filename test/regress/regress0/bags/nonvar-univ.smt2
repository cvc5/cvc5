; COMMAND-LINE: --sets-ext
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun x () (Bag Int))
(declare-fun P ((Bag Int)) Bool)

(assert (P x))
(assert (not (P (bag 0 1))))
(assert (>= (bag.count 1 x)))
(assert (not (>= (bag.count 0 (as set.universe (Bag Int))) 1)))

(check-sat)
