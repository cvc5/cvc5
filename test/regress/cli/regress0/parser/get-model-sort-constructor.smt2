; EXPECT: sat
; EXPECT: (
; EXPECT: )
(set-option :produce-models true)
(set-logic QF_UFLIRA)
(declare-sort FArray 2)
(check-sat)
(get-model)
