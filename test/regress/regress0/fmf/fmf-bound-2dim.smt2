; COMMAND-LINE: --fmf-bound
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun P (Int Int) Bool)

(declare-fun a () Int)
(assert (> a 10))

(assert (forall ((x Int) (y Int))
(=> (and (<= a x) (<= x (+ a 5)) (<= 14 y) (<= y (+ 7 x)))
(P x y))))
(assert (not (P 15 4)))

(check-sat)
