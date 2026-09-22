; COMMAND-LINE: --nl-cov
; EXPECT: sat
; REQUIRES: poly
(set-logic QF_NIRA)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (= (+ 75 (- (- (- a) (* (ite (= (* a (- a (- (ite (= (* a a) 0) 0 (- 1))))) (- 75 (* c c))) (* a 0) (* b b)) (- (to_int (* b b)))) a))) 1))
(check-sat)
