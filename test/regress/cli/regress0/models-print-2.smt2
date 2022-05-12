; the purpose of this test is to verify that there is a `as` term in the output.
; the scrubber searches for "(as @a" patterns.

; SCRUBBER: grep -o "(as @a"
; EXPECT: (as @a
; EXPECT: (as @a
(set-logic QF_UF)
(set-option :produce-models true)
(declare-sort Sort0 0)
(declare-fun f1 () Sort0)
(check-sat)
(get-model)
