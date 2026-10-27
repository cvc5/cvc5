; COMMAND-LINE: --debug-check-models
; EXPECT: sat
(set-logic ALL)
(set-option :produce-models true)
(declare-fun y () Int)
(assert (or (forall ((V String)) (= "a" (str.substr V 0 y))) (= y 0)))
(check-sat)
