; COMMAND-LINE: --incremental -q
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (> (+ (/ (- 2) a) (* 8 a)) 0))
(assert (<= b 0))
(assert (= (+ (* 4 a) (* 2 b)) 1))
(assert (>= (* b c) 0))
(check-sat)
(check-sat)
(check-sat)
(push)
(check-sat)
(pop)
(assert (>= c 1))
(check-sat)
