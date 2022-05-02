; COMMAND-LINE: --solve-bv-as-int=sum
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun t () Int)
(assert (= (+ t 1) (bv2nat ((_ int2bv 16) t))))
(check-sat)
