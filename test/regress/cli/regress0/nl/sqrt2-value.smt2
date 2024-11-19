; SCRUBBER: sed -e 's/(_ real_algebraic_number <.*>)/value/'
; REQUIRES: poly
; EXPECT: sat
; EXPECT: ((x value))
(set-option :produce-models true)
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= (* x x) 2))
(check-sat)
(get-value (x))
