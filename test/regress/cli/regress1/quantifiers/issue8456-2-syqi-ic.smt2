; COMMAND-LINE: --sygus-inst
; EXPECT: unsat
;; Unary AND is not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(assert (and (forall ((v (Array (_ BitVec 1) Bool))) (select v (_ bv0 1)))))
(check-sat)
