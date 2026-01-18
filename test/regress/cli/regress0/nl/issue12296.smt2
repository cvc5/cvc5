; EXPECT: sat
(set-logic ALL)
(set-info :smt-lib-version 2.6)
(define-fun in_range ((x Int)) Bool
  (and (<= (- 2147483648) x) (<= x 2147483647)))

(declare-const item Int)

(assert
  (not (=> (in_range item) (<= (* item item) 2147483647))))

(check-sat)
