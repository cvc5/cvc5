; COMMAND-LINE: --produce-difficulty
; EXPECT: sat
(set-logic QF_UFNRA)
(declare-fun s (Real Real) Real)
(declare-fun -- (Real Real) Real)
(declare-fun e (Real Real) Bool)
(declare-fun d (Real) Real)
(declare-fun s4 () Real)
(declare-fun s5 () Real)
(assert (and (e 0.0 (-- 0.0 (d 1.0))) (e 0.0 (-- (s 0.0 0.0) (d 0.0))) (= 1.0 (abs (* (- s4 s5) (- s5 (abs s5)))))))
(assert (= (d 0.0) (s s4 0.0)))
(check-sat)
