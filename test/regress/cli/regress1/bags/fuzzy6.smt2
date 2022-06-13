(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(declare-fun A () (Table Int Int))
(declare-fun c () Int)
(declare-fun d () (Tuple Int Int))
(assert
 (let ((double_c (+ c c)))
   (let ((formula (= A (bag (tuple c double_c) c))))
     (and (not (= formula (= A (bag (tuple c c) c))))
          (not (= formula (= A (bag (tuple 0 c) double_c))))))))

(check-sat)
