; SCRUBBER: sed -e 's/witness.*/witness/'
; EXPECT: sat
; EXPECT: ((x (witness
(set-option :produce-models true)
(set-logic ALL)
(declare-fun x () Real)
(assert (= (* x x) 2))
(check-sat)
(get-value (x))
