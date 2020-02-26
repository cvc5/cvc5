; COMMAND-LINE: --rewrite-divk
; EXPECT: sat
(set-logic QF_BVLIA)
(declare-fun t () Int)
(assert (= t (bv2nat ((_ int2bv 1) t))))
(check-sat)
