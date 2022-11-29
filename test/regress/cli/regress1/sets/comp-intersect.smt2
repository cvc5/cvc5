; DISABLE-TESTER: lfsc
; COMMAND-LINE: --sets-ext
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)

(declare-fun x () (Set Int))
(declare-fun y () (Set Int))

(assert (= x (set.comprehension ((z Int)) (> z 4) (* 5 z))))
(assert (= y (set.comprehension ((z Int)) (< z 10) (+ (* 5 z) 1))))

(assert (not (= (set.inter x y) (as set.empty (Set Int)))))

(check-sat)
