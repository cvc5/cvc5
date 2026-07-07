; EXPECT: sat
(set-logic ALL)
(declare-const x Int)
(declare-const x6 Int)
(declare-fun b () Int)
(assert (and (> x 0) (= 0 (+ (- 1) (* x6 x) (* b x6 x x6)))))
(check-sat)
