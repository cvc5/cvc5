; COMMAND-LINE: --relational-triggers --user-pat=use
; EXPECT: unsat
(set-logic ALL)
(declare-fun F (Int) Bool)
(assert (forall ((v Int)) (! (= (F 0) (< v 0)) :qid |outputbpl.194:24| :pattern ((F 0)))))
(check-sat)
