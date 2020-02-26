; SCRUBBER: sed -e 's/BOUND_VARIABLE_[0-9]*/BOUND_VARIABLE/; s/((x (choice ((BOUND_VARIABLE Real)) (or (= BOUND_VARIABLE.*/SUCCESS/'
; COMMAND-LINE: --produce-models --model-witness-choice --no-check-models
; EXPECT: sat
; EXPECT: SUCCESS
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun x () Real)
(assert (= (* x x) 2))
(check-sat)
(get-value (x))

