; COMMAND-LINE: --produce-unsat-cores --incremental
; EXPECT: sat
(set-logic QF_UFNIA)
(declare-const v10 Bool)
(declare-const i12 Int)
(declare-const i16 Int)
(push 1)
(assert (=> (<= (mod i12 38) i16) v10))
(check-sat)
