; EXPECT: sat
(set-logic QF_AX)
(declare-const x (Array Bool Bool))
(declare-const _x (Array Bool (Array Bool Bool)))
(declare-const x4 Bool)
(assert (and (select (select (store _x x4 x) true) false)))
(check-sat)
