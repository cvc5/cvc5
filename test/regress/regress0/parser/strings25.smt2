; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun s () String """")
; EXPECT: )

(set-logic QF_S)
(set-option :produce-models true)

(declare-fun s () String)

(assert (= s """"))

(check-sat)
(get-model)
