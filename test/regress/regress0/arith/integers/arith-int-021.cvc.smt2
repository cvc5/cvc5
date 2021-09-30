; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(assert (< (+ (+ (+ (* 8 x0) (* (- 27) x1)) (* 29 x2)) (* (- 13) x3)) 12))
(check-sat)
