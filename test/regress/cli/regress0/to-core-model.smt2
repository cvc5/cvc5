; COMMAND-LINE: --produce-models --check-models
; SCRUBBER: grep -E 'sat'
; EXPECT: sat
(set-logic ALL)
(set-option :produce-unsat-cores true)
(declare-fun x () Int)
(assert (> x 0))
(get-timeout-core)
(get-model)
