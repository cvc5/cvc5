;; Datatypes are not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-info :status unsat)
(declare-datatypes ((E 0)) (((c (a Bool)))))
(assert (forall ((v E)) (a v)))
(check-sat)
