; COMMAND-LINE: --dump-proofs --proof-format=cpc
; SCRUBBER: grep -o -E 'unsat|:rule eq_resolve' | sed 's/:rule //'
; EXPECT: unsat
; EXPECT: eq_resolve
(set-logic ALL)
(set-option :produce-proofs true)
(assert false)
(check-sat)
