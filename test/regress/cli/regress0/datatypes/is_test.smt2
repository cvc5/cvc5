;; Datatypes are not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-info :status unsat)
(declare-datatypes ((Unit 0)) (((u))))
(declare-fun x () Unit)
(assert (not ((_ is u) x)))
(check-sat)
