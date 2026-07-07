; EXPECT: sat
; EXPECT: (
; EXPECT: (distinct x 0)
; EXPECT: true
; EXPECT: )
; EXPECT: ((x (- 1)))
(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const x Int)
(assert (distinct x 0))
(check-sat-assuming (true))
(get-assertions)
(get-value (x))
