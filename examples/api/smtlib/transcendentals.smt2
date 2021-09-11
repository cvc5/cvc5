(set-logic QF_NRAT)
(declare-fun x () Real)
(declare-fun y () Real)

(assert (> x real.pi))
(assert (< x (* 2 real.pi)))
(assert (< (* y y) (sin x)))
(check-sat)
