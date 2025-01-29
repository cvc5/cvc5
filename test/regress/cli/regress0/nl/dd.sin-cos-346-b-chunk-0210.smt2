; COMMAND-LINE: --no-nl-cov
; EXPECT: sat
(set-logic ALL)
(declare-const x Real)
(declare-fun s () Real)
(assert (and (> s 0) (= 0.0 (* s s (+ (/ 1 9) (* x (/ 1 0)))))))
(check-sat)
