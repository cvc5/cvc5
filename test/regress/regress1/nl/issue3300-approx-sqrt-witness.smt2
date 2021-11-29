; SCRUBBER: sed -e 's/BOUND_VARIABLE_[0-9]*/BOUND_VARIABLE/; s/((x (witness ((BOUND_VARIABLE Real)) (.*/SUCCESS/'
; COMMAND-LINE: --produce-models --model-witness-value --no-check-models
; REQUIRES: poly
; EXPECT: sat
; EXPECT: SUCCESS
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun x () Real)
(assert (= (* x x) 2))
(check-sat)
(get-value (x))

