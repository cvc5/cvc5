; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun t () Int)
(assert (= (+ t 1) (ubv_to_int ((_ int_to_bv 16) t))))
(check-sat)
