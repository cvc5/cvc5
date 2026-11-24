; COMMAND-LINE: --check-proofs
; SCRUBBER: grep -E 'unsat'
; EXPECT: unsat
; External proof checking is disabled because get-timeout-core prints
; a core alongside the proof, interfering with proof extraction.
; DISABLE-TESTER: cpc
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun x () Int)
(assert (= 0 0))
(assert (>= x 564838384999))
(assert (= (/ x x x) 564838384999))
(get-timeout-core)
