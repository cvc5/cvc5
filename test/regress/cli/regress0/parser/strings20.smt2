; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun s () String "\u{5c}""")
; EXPECT: )

(set-logic QF_S)
(set-info :smt-lib-version 2.6)
(set-option :produce-models true)

(declare-fun s () String)

(assert (= s "\"""))

(check-sat)
(get-model)
