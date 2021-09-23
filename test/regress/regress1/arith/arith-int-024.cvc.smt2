; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(assert (= (+ (+ (+ (* 4 x0) (* 8 x1)) (* 27 x2)) (* (- 12) x3)) (- 5)))
(check-sat-assuming ( (not false) ))
