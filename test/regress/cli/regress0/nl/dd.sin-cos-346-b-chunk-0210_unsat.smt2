; COMMAND-LINE: --no-nl-cov
; EXPECT: unsat
(set-logic QF_NRA)
(declare-fun s () Real)
(declare-fun k () Real)
(assert (and (> s 0) (= 3 (* k k)) (= 0.0 (* s s (+ 1.0 (* k k) (* s s (+ (* k (/ 1 13)) (* s k k (/ 1 47)))))))))
(check-sat)
