(set-logic QF_SLIA)
(set-info :status unsat)
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

(assert (distinct x y z "B" "C" "D" "E"))

(check-sat)
