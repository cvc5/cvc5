; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(assert (<= (+ (+ (+ (* 29 x0) (* (- 19) x1)) (* 23 x2)) (* 15 x3)) 9))
(check-sat)
