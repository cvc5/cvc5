; COMMAND-LINE: --learned-rewrite
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-const a Real)
(declare-const b Int)
(assert (> a (/ (to_real b) (to_real 0))))
(check-sat)
