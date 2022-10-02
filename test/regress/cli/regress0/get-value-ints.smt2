; EXPECT: sat
; EXPECT: ((pos 1) (zero 0) (neg (- 6)))
(set-info :smt-lib-version 2.6)
(set-option :produce-models true)
(set-logic QF_LIA)

; This output changes if the smt2 printer output for Ints changes.

(declare-fun pos () Int)
(declare-fun zero () Int)
(declare-fun neg () Int)

(assert (= pos 1))
(assert (= zero 0))
(assert (= neg (- 6)))

(check-sat)
(get-value (pos zero neg))
