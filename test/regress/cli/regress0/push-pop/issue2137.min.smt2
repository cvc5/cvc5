; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Real)
(declare-fun b () Bool)
(assert (< 0 a))
(assert (xor b (< 0 a 0) false))
(check-sat)
(assert (not b))
(check-sat)
