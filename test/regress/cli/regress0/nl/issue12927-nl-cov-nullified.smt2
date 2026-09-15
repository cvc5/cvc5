; REQUIRES: poly
; COMMAND-LINE: --nl-ext=none --nl-cov
; EXPECT: sat
; McCallum's projection operator, which the coverings solver uses by default,
; is not sound here since a polynomial is nullified over the current
; assignment. The coverings solver must only exclude the sample point then.
(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x () Real)
(declare-fun z () Real)
(assert (= 0 (* (- x2 1) (- x1 1) (- x1 1) (- x1 1))))
(assert (= 0 (* x2 x2 x2)))
(assert (> x 0))
(assert (> (- z (- x 1)) 0))
(assert (< (+ (* z z z) (* 2 (+ x2 (* (- x 1) (- x 1) (- x 1)))) (* z (- 3) (+ (- x1 1) (* (- x 1) (- x 1))))) 0))
(check-sat)
