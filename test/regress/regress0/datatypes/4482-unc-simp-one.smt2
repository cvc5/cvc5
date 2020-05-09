(set-logic ALL)
(declare-fun a () Tuple)
(assert (distinct a mkTuple))
(check-sat)
