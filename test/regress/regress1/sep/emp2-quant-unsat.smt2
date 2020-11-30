; COMMAND-LINE: --quant-epr
; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun u () U)
(declare-heap (U U))

(assert (sep (not (_ emp U U)) (not (_ emp U U))))

(assert (forall ((x U) (y U)) (= x y)))

(check-sat)
