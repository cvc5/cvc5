; EXPECT: sat
; EXPECT: ((pos_int (/ 3 1)) (pos_rat (/ 1 3)) (zero (/ 0 1)) (neg_rat (/ (- 2) 3)) (neg_int (/ (- 2) 1)))
(set-info :smt-lib-version 2.0)
(set-option :produce-models true)
(set-logic QF_LRA)

; This output changes if the smt2 printer output for Reals changes.
(declare-fun pos_int () Real)
(declare-fun pos_rat () Real)
(declare-fun zero () Real)
(declare-fun neg_rat () Real)
(declare-fun neg_int () Real)

(assert (= pos_int 3))
(assert (= pos_rat (/ 1 3)))
(assert (= zero 0))
(assert (= neg_rat (/ (- 2) 3)))
(assert (= neg_int (- 2)))

(check-sat)
(get-value (pos_int pos_rat zero neg_rat neg_int))
