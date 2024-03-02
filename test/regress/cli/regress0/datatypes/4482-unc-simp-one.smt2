;; Datatypes are not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-info :status unsat)
(declare-fun a () UnitTuple)
(assert (distinct a tuple.unit))
(check-sat)
