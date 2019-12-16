; COMMAND-LINE: --sets-ext
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)

(declare-fun x () (Set Int))

(assert (subset x (comprehension ((z Int)) (> z 0) z)))

(assert (member 0 x))

(check-sat)
