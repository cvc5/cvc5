; SCRUBBER: sed -e 's/(_ real_algebraic_number.*/(_ real_algebraic_number/'
; REQUIRES: poly
; EXPECT: sat
; EXPECT: ((x (_ real_algebraic_number
(set-option :produce-models true)
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= (* x x) 2))
(check-sat)
(get-value (x))
