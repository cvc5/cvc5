; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic QF_NIA)
(declare-const x Int)
(declare-const _x Int)
(assert (= x (* _x (mod (int.pow2 _x) x))))
(assert ((_ divisible 125436566) _x))
(check-sat)
