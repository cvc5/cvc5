; SCRUBBER: grep -v -E 'sat'
; EXPECT: sat
(set-logic ALL)
(set-option :produce-unsat-cores true)
(declare-fun x () Int)
(assert (> x 0))
(get-timeout-core)
(get-model)
