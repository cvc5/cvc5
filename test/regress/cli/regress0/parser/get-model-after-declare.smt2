; EXPECT: sat
; EXPECT: (error "cannot get model unless after a SAT or UNKNOWN response.")
(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
(declare-fun y () Int)
(get-model)
