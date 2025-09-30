(set-logic ALL)
(set-info :status sat)
(define-fun predicate
  (
     (t1 (Tuple Int Int Int)) 
     (t2 (Tuple Int Int Int)) 
     (t3 (Tuple Int Int Int))) Bool
 (and 
   (= ((_ tuple.select 0) t1) (+ ((_ tuple.select 0) t2) ((_ tuple.select 0) t3)))
   (= ((_ tuple.select 1) t1) (+ ((_ tuple.select 1) t2) ((_ tuple.select 1) t3)))
   (= ((_ tuple.select 2) t1) (+ ((_ tuple.select 2) t2) ((_ tuple.select 2) t3)))
 )
)
(declare-const v (Tuple Int Int Int))
(declare-const v1 (Tuple Int Int Int))
(declare-const v2 (Tuple Int Int Int))
(assert (predicate v v1 v2))
(assert (distinct v v1 v2))
(assert (int.star-contains ((x Int) (y Int) (z Int)) (= x (+ y z)) v))
(assert (int.star-contains ((x Int) (y Int) (z Int)) (= x (+ y z)) v1))
(assert (int.star-contains ((x Int) (y Int) (z Int)) (= x (+ y z)) v2))

(check-sat)
