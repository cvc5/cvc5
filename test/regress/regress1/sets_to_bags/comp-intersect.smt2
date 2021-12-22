; COMMAND-LINE: --sets-ext
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)

(declare-fun x () (Bag Int))
(declare-fun y () (Bag Int))

(assert (= x (set.comprehension ((z Int)) (> z 4) (* 5 z))))
(assert (= y (set.comprehension ((z Int)) (< z 10) (+ (* 5 z) 1))))

(assert (not (= (bag.inter_min x y) (as bag.empty (Bag Int)))))

(check-sat)
