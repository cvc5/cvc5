; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(assert
 (forall ((a Int) (b Int))
 (or (< a (/ 3 b (- 2)))
  (forall ((c Int)) (or (<= c b) (>= c a))))))
(check-sat)
