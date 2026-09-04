; REQUIRES: normaliz
; Nonnegativity is not built into int.star-contains: the lambda constrains
; its variables (or not) itself. Here the summands are fixed at -1, so the
; star closure is {0, -1, -2, ...} and a = -5 is the sum of five summands.
(set-logic HO_ALL)
(set-info :status sat)
(set-option :quiet true)
(declare-const a Int)
(assert (= a (- 5)))
(assert (int.star-contains (lambda ((x Int)) (= x (- 1))) a))
(check-sat)
