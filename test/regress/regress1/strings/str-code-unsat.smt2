(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

(assert (>= (str.to_code x) 65))
(assert (<= (str.to_code x) 75))

(assert (>= (str.to_code y) 65))
(assert (<= (str.to_code y) 75))

(assert (>= (str.to_code z) 65))
(assert (<= (str.to_code z) 75))

(assert (= (+ (str.to_code x) (str.to_code y)) 140))
(assert (= (+ (str.to_code x) (str.to_code z)) 140))

(assert (distinct x y z))

(check-sat)
