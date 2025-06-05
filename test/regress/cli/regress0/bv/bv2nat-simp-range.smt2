; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun t () (_ BitVec 16))
(assert (not (and (<= 0 (ubv_to_int t)) (< (ubv_to_int t) 65536))))
(check-sat)
