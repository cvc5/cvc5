; COMMAND-LINE: --sets-ext
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)

(declare-fun x () (Set Int))
(declare-fun y () (Set Int))

(assert (= x (comprehension ((z Int)) (> z 4) (* 5 z))))
(assert (= y (comprehension ((z Int)) (< z 10) (+ (* 5 z) 1))))

(assert (not (= (intersection x y) (as emptyset (Set Int)))))

(check-sat)
