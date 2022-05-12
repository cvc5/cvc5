; DISABLE-TESTER: lfsc
; COMMAND-LINE: --bv-solver=bitblast
; EXPECT: unsat
(set-logic QF_FPLRA)
(declare-fun fpv5 () Float32)
(assert (fp.eq (fp.mul RTP fpv5 fpv5) ((_ to_fp 8 24) RTN 0.04)))
(check-sat)
