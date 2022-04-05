; EXPECT: unsat
; EXPECT: (error "Cannot get model unless after a SAT or UNKNOWN response.")
(set-option :incremental false)
(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(check-sat-assuming ( (not (= x x)) ))
(get-model)
