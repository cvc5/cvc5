; COMMAND-LINE: --quant-epr
; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun u () U)

(assert (sep (not (emp u u)) (not (emp u u))))

(assert (forall ((x U) (y U)) (= x y)))

(check-sat)
