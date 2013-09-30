; COMMAND-LINE: --no-check-models
; EXPECT: sat
; EXIT: 10
;
(set-logic QF_S)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(declare-fun w1 () String)
(declare-fun w2 () String)

(assert (= (str.++ x y z) (str.++ x z y)))
(assert (= (str.++ x w z) (str.++ x z w)))
(assert (not (= y w)))
(assert (> (str.len z) 0))

(check-sat)
