; REQUIRES: normaliz
(set-logic ALL)
(set-info :status unsat)

(declare-fun A () Int)
(declare-fun B () Int)
(declare-fun C () Int)
(assert (>= A 0))
(assert (>= B 0))
(assert (>= C 0))
(assert (distinct C (+ A B)))
(assert 
 (int.star-contains 
   ((a Int) (b Int) (c Int))
   (and
     (>= a 0) (>= b 0) (>= c 0)
     (= c (+ a b))
   )
   (tuple A B C)
 )
)
(check-sat)