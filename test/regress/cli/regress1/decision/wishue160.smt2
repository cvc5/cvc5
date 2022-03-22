; COMMAND-LINE: --decision=justification
; EXPECT: sat
(set-logic ALIA)
(set-option :repeat-simp true)
(set-option :sygus-rr-synth-check true)
(declare-fun v6 () Bool)
(declare-const arr-7579056739068271278_-8074447279386590332-0 (Array Bool Int))
(assert (= false false false (= arr-7579056739068271278_-8074447279386590332-0 (store arr-7579056739068271278_-8074447279386590332-0 v6 746)) false false false))
(check-sat)
