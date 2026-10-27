; REQUIRES: unrestricted-mode
; COMMAND-LINE: --dump-proofs --proof-format=cpc
; SCRUBBER: grep -o -E 'unsat|:rule eq_resolve' | sed 's/:rule //'
; EXPECT: unsat
; EXPECT: eq_resolve
;; Note the cpc tester does not apply to this test, since its expected output
;; is not plain unsat. See assume-false-final-step-check.smt2 for the test that
;; checks the resulting proof with ethos.
(set-logic ALL)
(set-option :produce-proofs true)
(assert false)
(check-sat)
