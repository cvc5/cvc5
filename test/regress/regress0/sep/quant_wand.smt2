; COMMAND-LINE: --full-saturate-quant
; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-const u Int)

(assert (emp 0 0))

(assert 
(forall ((y Int)) 
(not (wand (pto u 5) (and (= y 42) (pto u 5))))
))

(check-sat)
