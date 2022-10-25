; COMMAND-LINE: -q
(set-logic ALL)
(set-info :status sat)
(declare-fun a () Real)
(assert (and (forall ((a Real)) (= 0.0 (/ 0.0 0.0)))))
(assert (> (/ a a) (/ (* a a) 0.0)))
(check-sat)
