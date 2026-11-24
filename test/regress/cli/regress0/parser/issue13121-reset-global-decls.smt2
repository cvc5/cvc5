; COMMAND-LINE: --incremental
; EXPECT: false
; EXPECT: sat
(set-option :global-declarations true)
(set-logic QF_LIA)
(reset)
(get-option :global-declarations)
(set-logic QF_LIA)
(push 1)
(declare-const y Int)
(pop 1)
; y is no longer declared since global declarations is false after the reset
(declare-const y Int)
(assert (> y 0))
(check-sat)
