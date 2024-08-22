; DISABLE-TESTER: lfsc
; COMMAND-LINE: --sets-ext
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)

(declare-fun x () (Set Int))

(assert (set.subset x (set.comprehension ((z Int)) true (* 2 z))))

(declare-fun a () Int)
(declare-fun b () Int)

(assert (= a (+ (* 8 b) 1)))
(assert (set.member a x))

(check-sat)
