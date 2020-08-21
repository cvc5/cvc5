; EXPECT: sat
; EXPECT: ((pos_int 5) (pos_real_int_value (/ 3 1)) (pos_rat (/ 1 3)) (zero (/ 0 1)) (neg_rat (/ (- 2) 3)) (neg_real_int_value (/ (- 2) 1)) (neg_int (- 6)))
(set-info :smt-lib-version 2.0)
(set-option :produce-models true)
(set-logic QF_LIRA)

; This output changes if the smt2 printer output for Reals_Ints changes.

(declare-fun pos_int () Int)
(declare-fun pos_real_int_value () Real)
(declare-fun pos_rat () Real)
(declare-fun zero () Real)
(declare-fun neg_rat () Real)
(declare-fun neg_real_int_value () Real)
(declare-fun neg_int () Int)

(assert (= pos_int 5))
(assert (= pos_real_int_value 3))
(assert (= pos_rat (/ 1 3)))
(assert (= zero 0))
(assert (= neg_rat (/ (- 2) 3)))
(assert (= neg_real_int_value (- 2)))
(assert (= neg_int (- 6)))

(check-sat)
(get-value (pos_int pos_real_int_value pos_rat zero neg_rat neg_real_int_value neg_int))
