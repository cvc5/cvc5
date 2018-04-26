(set-logic QF_S)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

(assert (>= (str.code x) 65))
(assert (<= (str.code x) 75))

(assert (>= (str.code y) 65))
(assert (<= (str.code y) 75))

(assert (>= (str.code z) 65))
(assert (<= (str.code z) 75))

(assert (= (+ (str.code x) (str.code y)) 140))
(assert (= (+ (str.code x) (str.code z)) 141))

(assert (distinct x y z "B" "C" "D" "AA"))

(check-sat)
