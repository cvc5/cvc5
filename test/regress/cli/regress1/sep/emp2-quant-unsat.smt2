; COMMAND-LINE: --quant-epr
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun u () U)
(declare-heap (U U))

(assert (sep (not sep.emp) (not sep.emp)))

(assert (forall ((x U) (y U)) (= x y)))

(check-sat)
