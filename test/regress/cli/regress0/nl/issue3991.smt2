; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
(set-logic QF_NIA)
(declare-const i7 Int)
(check-sat)
(declare-const v18 Bool)
(assert (and (= i7 93) (or (> 19 i7) v18) v18))
(check-sat)
(assert (> 19 i7))
(assert (> (div i7 0) 0))
(check-sat)
