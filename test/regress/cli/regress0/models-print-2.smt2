; the purpose of this test is to verify that name of the uninterpreted sort appears in the constant output.
; For example, if the sort is Sort0, then scrubber searches for "(as @Sort0_" patterns.

; SCRUBBER: grep -o "(as @Sort0_"
; EXPECT: (as @Sort0_
; EXPECT: (as @Sort0_
(set-logic QF_UF)
(set-option :produce-models true)
(declare-sort Sort0 0)
(declare-fun f1 () Sort0)
(check-sat)
(get-model)
