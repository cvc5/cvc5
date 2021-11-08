; SCRUBBER: sed -e 's/witness.*/witness/'
; COMMAND-LINE: --no-check-models
; EXPECT: sat
; EXPECT: ((x (witness
(set-option :produce-models true)
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= (* x x) 2))
(check-sat)
(get-value (x))
