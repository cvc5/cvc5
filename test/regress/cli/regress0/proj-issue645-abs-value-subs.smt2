; SCRUBBER: sed -e 's/((x.*//g'
; EXPECT: sat
(set-logic ALL)
(set-option :produce-models true)
(set-option :abstract-values true)
(declare-const x (Array Bool Bool))
(check-sat)
(get-value (x x))
