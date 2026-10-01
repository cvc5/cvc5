; REQUIRES: poly
; COMMAND-LINE: --nl-cov -q
; EXPECT: sat
(set-logic ALL)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (= 74 (- b (* (ite (= (* c c (- (ite (= 75 (* b b)) 0 (- 1)))) (- 5 (* b b))) (* c 0) (* a a)) (- (to_int (* a a)))))))
(check-sat)
