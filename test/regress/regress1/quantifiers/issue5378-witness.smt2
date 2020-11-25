; COMMAND-LINE: --sygus-inst
; EXPECT: unsat
(set-logic ALL)
(assert (forall ((a Int) (b Int)) (or (> a (/ 0 b)) (exists ((c Int)) (< a c b)))))
(check-sat)
