; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (> (+ (/ (- 2.0) a) (* 8.0 a)) 0.0))
(assert (<= b 0.0))
(assert (= (+ (* 4.0 a) (* 2.0 b)) 1.0))
(assert (>= (* b c) 0.0))
(check-sat)
(check-sat)
(check-sat)
(push)
(check-sat)
(pop)
(assert (>= c 1.0))
(check-sat)
