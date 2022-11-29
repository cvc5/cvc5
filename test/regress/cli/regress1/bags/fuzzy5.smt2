(set-logic ALL)
(set-option :produce-models true)
(set-info :status sat)
(declare-fun A () (Table Int Int))
(declare-fun c () Int)
(declare-fun d () (Tuple Int Int))

(assert
 (let ((c_plus_1 (+ c 1)))
   (and
    (not
     (= (= A (bag (tuple 0 c) (+ c c)))
        (= A (bag.difference_remove (bag d c) A))))
    (not
     (= (= A (bag (tuple 0 1) c_plus_1))
        (= A (bag (tuple c 1) c_plus_1)))))))

;(assert (= A (bag (tuple 0 1) 2)))
;(assert (= c 1))
;(assert (= d (tuple 0 1)))
(check-sat)