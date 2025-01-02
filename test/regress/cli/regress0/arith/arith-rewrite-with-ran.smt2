; REQUIRES: poly
; EXPECT: sat
(set-logic QF_NRA)
(declare-const x Bool)
(declare-const y Real)
(declare-fun b () Real)
(declare-fun a () Bool)
(declare-fun c () Real)
(declare-fun d () Real)
(declare-fun e () Real)
(declare-fun f () Real)
(declare-fun g () Real)
(assert (and (not a) (or x (= 1 e)) (or x (= 0.0 g)) (= 0.0 (+ b y d)) (or a (= 0.0 (+ c y))) (= 0.0 (+ 1.0 f y)) (= 0.0 (+ 1.0 b (* 49.0 f))) (= 0.0 (+ e (* g y) (* f f (- 49.0))))))
(check-sat)
