; the purpose of this test is to verify that there is a `as` term in the output.
; the scrubber excludes all lines without "(as @", and replaces this pattern by "AS".

; SCRUBBER: sed -e 's/.*(as @.*/AS/; /sat/d; /cardinality/d; /^($/d; /^)$/d'
; EXPECT: AS
(set-logic QF_UF)
(set-option :produce-models true)
(declare-sort Sort0 0)
(declare-fun f1 () Sort0)
(check-sat)
(get-model)
