; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-const x Bool)
(declare-const v Real)
(assert (exists ((t Real)) (not (=> (= 0.0 (+ 1.0 (/ (* v v) 0.0))) (and (and x x) (= v 0.0))))))
(check-sat)
