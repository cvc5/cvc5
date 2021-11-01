; SCRUBBER: sed -e 's/witness.*/witness/'
; COMMAND-LINE: --no-check-models
; EXPECT: sat
; EXPECT: ((x (witness
(set-logic QF_NRA)
(set-option :produce-models true)
(set-logic ALL)
(declare-fun x () Real)
(assert (= (* x x) 2))
(check-sat)
(get-value (x))
