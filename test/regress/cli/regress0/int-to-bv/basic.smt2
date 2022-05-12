; COMMAND-LINE: --solve-int-as-bv=5
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
; Tests the conversion of negative constants and non-linear multiplication
(assert (= (- 2) (* x y)))
; Operators with more than two children
(assert (= 8 (* x x x)))
(set-info :status sat)
(check-sat)
