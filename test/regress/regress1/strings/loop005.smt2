(set-logic QF_SLIA)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)

;(assert (= (str.++ x y z) (str.++ x z y)))
;(assert (= (str.++ x w z) (str.++ x z w)))

(assert (= (str.++ y z) (str.++ z y)))
(assert (= (str.++ w z) (str.++ z w)))

(assert (not (= y w)))
(assert (> (str.len z) 0))

(check-sat)
