; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(assert (>= (+ (+ (+ (* (- 19) x0) (* (- 29) x1)) (* 2 x2)) (* 26 x3)) 3))
(check-sat)
