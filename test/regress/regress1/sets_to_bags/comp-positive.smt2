; COMMAND-LINE: --sets-ext
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)

(declare-fun x () (Bag Int))

(assert (bag.subbag x (set.comprehension ((z Int)) (> z 0) z)))

(assert (bag.count 0 x))

(check-sat)
