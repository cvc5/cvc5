; COMMAND-LINE: --sets-ext
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)

(declare-fun x () (Bag Int))

(assert (bag.subbag x (bag.comprehension ((z Int)) (> z 0) z)))

(assert (>= (bag.count 0 x) 1))

(check-sat)
