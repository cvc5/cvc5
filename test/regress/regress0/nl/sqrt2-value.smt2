; SCRUBBER: sed -e 's/choice.*/choice/'
; EXPECT: sat
; EXPECT: ((x (choice
(set-option :produce-models true)
(set-logic ALL)
(declare-fun x () Real)
(assert (= (* x x) 2))
(check-sat)
(get-value (x))
