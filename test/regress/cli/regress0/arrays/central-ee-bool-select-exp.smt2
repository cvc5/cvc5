; COMMAND-LINE: --ee-mode=central
; EXPECT: sat
(set-logic QF_AX)
(declare-const B (Array Bool Bool))
(declare-const b1 Bool)
(declare-const b2 Bool)
(assert (=> (select (store B b1 b2) (not b2)) b1))
(assert (=> b1 b2))
(assert (= (select B b2) (not b2)))
(check-sat)
