;; Datatypes are not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-info :status unsat)
(declare-datatype Box (par (A) ((box (unbox A)))))
(assert (forall ((xy (Box Bool))) (unbox xy)))
(check-sat)
