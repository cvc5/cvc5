; REQUIRES: unrestricted-mode
; COMMAND-LINE: --incremental --rlimit-per=10000 --no-debug-check-models
; EXPECT: sat
; EXPECT: unknown
(set-logic ALL)
(declare-const x Real)
(push 1)
(assert (< x 0))
(assert (> (exp x) 0))
(check-sat)
(pop 1)
(assert (>= x (- 3)))
(assert (<= x (- (/ 299 100))))
(assert (> (* (exp x) (exp x)) (/ 1 300)))
(check-sat)
