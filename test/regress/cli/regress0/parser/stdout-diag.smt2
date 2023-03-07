; Ensure that no `stdout` or `"stdout"` file is created
; SCRUBBER: ls stdout || ls \"stdout\" || echo success
; EXPECT: success
(set-option :global-declarations true)
(set-option :diagnostic-output-channel "stdout")
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun s0 () Bool)
(assert s0)
(check-sat)
