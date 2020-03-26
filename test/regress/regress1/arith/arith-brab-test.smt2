; COMMAND-LINE: --arith-brab
; COMMAND-LINE: --no-arith-brab
; EXPECT: sat
(set-logic ALL)

(declare-fun x1 () Real)
(declare-fun y1 () Real)
(declare-fun m1 () Real)
(declare-fun b1 () Real)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (= y1 (+ b1 (* m1 x1))))
(assert (= x1 (/ m1 (- y1 b1))))
(assert (= b1 1.25))
(assert (= m1 (/ 1 3)))

(assert (and (> x x1) (> y y1)))

(check-sat)
(exit)

