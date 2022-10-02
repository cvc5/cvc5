; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun t () (_ BitVec 16))
(assert (not (and (<= 0 (bv2nat t)) (< (bv2nat t) 65535))))
(check-sat)
