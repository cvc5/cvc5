; REQUIRES: unrestricted-mode
; EXPECT: unsat
(set-logic ALL)
(set-option :dt-infer-as-lemmas true)
(set-option :debug-check-models true)
(declare-datatypes ((d 0)) (((c))))
(declare-const x d)
(check-sat-assuming ((distinct c x)))
