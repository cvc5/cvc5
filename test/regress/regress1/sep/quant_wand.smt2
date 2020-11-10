; COMMAND-LINE: --full-saturate-quant
; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(set-info :status unsat)
(declare-heap (Int Int))

(declare-const u Int)

(assert (_ emp Int Int))

(assert 
(forall ((y Int)) 
(not (wand (pto u 5) (and (= y 42) (pto u 5))))
))

(check-sat)
