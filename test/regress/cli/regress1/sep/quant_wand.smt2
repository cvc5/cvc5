; COMMAND-LINE: --full-saturate-quant
; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-info :status unsat)
(declare-heap (Int Int))

(declare-const u Int)

(assert sep.emp)

(assert
(forall ((y Int))
(not (wand (pto u 5) (and (= y 42) (pto u 5))))
))

(check-sat)
