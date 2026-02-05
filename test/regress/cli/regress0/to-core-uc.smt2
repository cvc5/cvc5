; COMMAND-LINE: --produce-proofs --check-proofs
; SCRUBBER: grep -E 'unsat'
; EXPECT: unsat
; DISABLE-TESTER: lfsc
; DISABLE-TESTER: cpc
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-option :produce-unsat-cores true)
(declare-fun x () Int)
(assert (> x 0))
(assert (< x 0))
(get-timeout-core)
(get-unsat-core)
(get-unsat-assumptions)
