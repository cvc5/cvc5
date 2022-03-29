; SCRUBBER: sed -e 's/((x (_ real_algebraic_number .*/((x (_ real_algebraic_number/'
; COMMAND-LINE: --produce-models
; REQUIRES: poly
; EXPECT: sat
; EXPECT: ((x (_ real_algebraic_number
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun x () Real)
(assert (= (* x x) 2))
(check-sat)
(get-value (x))

