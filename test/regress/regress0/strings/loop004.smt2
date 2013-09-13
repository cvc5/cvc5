; COMMAND-LINE: --no-check-models
; EXPECT: sat
; EXIT: 10
;
(set-logic ALL_SUPPORTED)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(declare-fun w1 () String)
(declare-fun w2 () String)

(assert (= (str.++ x y z) (str.++ y z x)))

(check-sat)
