(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)

(assert (>= (str.to_code x) 65))
(assert (<= (str.to_code x) 75))

(assert (>= (str.to_code y) 65))
(assert (<= (str.to_code y) 75))

(assert (>= (str.to_code z) 65))
(assert (<= (str.to_code z) 75))

(assert (= (str.len w) 1))

(assert (= (+ (str.to_code x) (str.to_code y)) 140))
(assert (= (+ (str.to_code x) (str.to_code z)) 141))

(assert (distinct x y z w "A" "B" "C" "D" "AA"))

(check-sat)
