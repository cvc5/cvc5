; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
(set-logic QF_BV)
(declare-fun x0 () (_ BitVec 3))
(assert (not (= #b001 x0)))
(assert (bvult #b000 x0))
(check-sat)
(check-sat)
