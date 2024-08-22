; DISABLE-TESTER: lfsc
; COMMAND-LINE: --sets-ext
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)

(declare-fun x () (Set Int))

(assert (set.subset x (set.comprehension ((z Int)) (> z 0) z)))

(assert (set.member 0 x))

(check-sat)
