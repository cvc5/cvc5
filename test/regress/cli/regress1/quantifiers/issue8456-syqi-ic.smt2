; COMMAND-LINE: --sygus-inst
; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(declare-sort I 0)
(declare-fun e () I)
(declare-fun ex () I)
(declare-fun t () I)
(declare-fun r () I)
(assert (distinct e ex))
(assert (forall ((xt I)) (exists ((E I)) (= xt t))))
(assert (or x (= t r)))
(check-sat)
