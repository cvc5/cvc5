; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: sat
(set-logic QF_UFNRA)
(declare-fun r () Real)
(declare-fun u (Real Real) Bool)
(assert (u 0.0 (* r r)))
(push)
(assert (and (< r 0.0) (< 0.0 r)))
(check-sat)
(pop)
(check-sat)