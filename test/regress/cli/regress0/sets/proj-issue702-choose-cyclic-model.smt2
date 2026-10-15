; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(declare-const x (Set Int))
(assert (= (set.choose x) (int.pow2 (div (set.choose x) (set.choose x)))))
(assert (set.member (set.card x) x))
(check-sat)
