(declare-fun x () Real)
(assert (distinct x (sin 4.0)))
(check-sat)
