; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(assert
 (forall ((a Int) (b Int))
 (or (< (to_real a) (/ 3.0 (to_real b) (- 2.0)))
  (forall ((c Int)) (or (<= c b) (>= c a))))))
(check-sat)
