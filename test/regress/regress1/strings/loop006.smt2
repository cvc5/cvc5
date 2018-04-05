(set-logic QF_S)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(declare-fun w1 () String)
(declare-fun w2 () String)

;(assert (= (str.++ x y) (str.++ y x)))

(assert (not (= (str.++ x y) (str.++ y x))))

(check-sat)
