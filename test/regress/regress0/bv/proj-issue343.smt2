; EXPECT: sat
; COMMAND-LINE: -q
(set-logic ALL)
(set-option :solve-bv-as-int bv)
(declare-const _x8 Real)
(assert (distinct real.pi _x8))
(check-sat)
