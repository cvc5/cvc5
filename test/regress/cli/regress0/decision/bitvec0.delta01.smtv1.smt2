; COMMAND-LINE: --decision=justification
; EXPECT: unsat
(set-option :incremental false)
(set-info :status unknown)
(set-logic QF_BV)
(declare-fun t () (_ BitVec 32))
(check-sat-assuming ( (not (ite (= ((_ extract 4 0) t) ((_ extract 6 2) t)) (and (= ((_ extract 6 6) t) ((_ extract 0 0) t)) (= ((_ extract 1 1) t) ((_ extract 5 5) t))) true)) ))
