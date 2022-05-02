; COMMAND-LINE: --sygus-inst --strings-exp
; EXPECT: unsat
(set-logic ALL)
(assert (forall ((a Int) (b Int)) (or (> (to_real a) (/ 0.0 (to_real b))) (exists ((c Int)) (< a c b)))))
(check-sat)
