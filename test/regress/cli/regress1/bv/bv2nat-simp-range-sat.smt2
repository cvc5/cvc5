; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun t () (_ BitVec 16))
(assert (not (and (<= 0 (ubv_to_int t)) (< (ubv_to_int t) 65535))))
(check-sat)
