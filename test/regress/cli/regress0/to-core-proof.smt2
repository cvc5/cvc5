; COMMAND-LINE: --produce-proofs --check-proofs
; SCRUBBER: grep -E 'unsat'
; EXPECT: unsat
; External proof checking is disabled because get-timeout-core prints
; a core alongside the proof, interfering with proof extraction.
; DISABLE-TESTER: cpc
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-option :produce-unsat-cores true)
(declare-fun x () Int)
(assert (> x 0))
(assert (< x 0))
(get-timeout-core)
(get-proof)
