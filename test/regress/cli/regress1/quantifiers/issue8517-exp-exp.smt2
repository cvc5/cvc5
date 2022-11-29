; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(declare-const x Bool)
(declare-const x1 Bool)
(assert (forall ((r Real)) (= x (and x1 (= r 2.0) (= 0.0 (exp (exp 1.0))) (= 3.0 (/ (- r) (- r)))))))
(check-sat)
