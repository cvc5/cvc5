; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun v () Real)
(declare-fun a () (Array Real Real))
(assert (exists ((V Real)) (or (and (= 0.0 (/ 0.0 v)) (< 0.0 (/ 0.0 v))) (= 1.0 (select (store a (/ (+ 0.0 real.pi) 0.0) 0.0) 0.0)))))
(check-sat)
