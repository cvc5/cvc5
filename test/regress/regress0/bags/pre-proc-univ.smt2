; COMMAND-LINE: --sets-ext
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () (Bag Int))

(assert (= x (bag.union_disjoint (bag 0 1) (bag 1 1))))

(assert (not (>= (bag.count 0 (as set.universe (Bag Int))) 1)))

(check-sat)
