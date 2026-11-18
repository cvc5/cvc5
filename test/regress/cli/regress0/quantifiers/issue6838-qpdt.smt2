; Logos does not support parametric datatype declarations.
; DISABLE-TESTER: cpc-logos
(set-logic ALL)
(set-info :status unsat)
(declare-datatype Box (par (A) ((box (unbox A)))))
(assert (forall ((xy (Box Bool))) (unbox xy)))
(check-sat)
