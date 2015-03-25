; EXPECT: sat
; EXPECT: (model
; EXPECT: (define-fun s () String "\"")
; EXPECT: )

(set-logic QF_S)
(set-info :smt-lib-version 2.0)
(set-option :produce-models true)

(declare-fun s () String)

(assert (= s "\""))

(check-sat)
(get-model)
