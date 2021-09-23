; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(assert (> (+ (+ (+ (* (- 24) x0) (* 25 x1)) (* (- 28) x2)) (* 31 x3)) 18))
(check-sat-assuming ( (not false) ))
