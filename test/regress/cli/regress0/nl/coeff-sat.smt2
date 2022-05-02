; EXPECT: sat
(set-logic QF_NRA)
(set-info :status sat)

(declare-fun a () Real)
(declare-fun b () Real)

(assert (> a 0))
(assert (> b 0))

(assert (>= a (* 3 b)))

(assert (< (* a a) (* 11 b b)))

(check-sat)
