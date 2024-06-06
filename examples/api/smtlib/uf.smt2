(set-logic QF_UF)

(declare-sort U 0)

(declare-const x U)
(declare-const y U)

(declare-fun f (U) U)
(declare-fun p (U) Bool)

(assert (= x (f x)))
(assert (= y (f y)))
(assert (not (p (f x))))
(assert (p (f y)))

(check-sat)

