(set-logic QF_S)
(set-info :status sat)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

;plandowski p469 1
(assert (= (str.++ x "ab" y) (str.++ y "ba" z)))
(assert (= z (str.++ x y)))
(assert (not (= (str.++ x "a") (str.++ "a" x))))

(check-sat)

