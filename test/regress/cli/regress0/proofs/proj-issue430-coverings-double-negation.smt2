; REQUIRES: poly
; EXPECT: unsat
; EXPECT: unsat
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (> 0.0 (+ 1 (* x (+ 1 x)))))
(check-sat)

(reset)

(set-logic QF_NRA)
(declare-fun skoD () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (not (<= (* skoY (+ (+ 2 (* skoD 2)) (* skoY (- 1)))) (+ (+ 1 (* skoD (+ 2 skoD))) (* skoX skoX)))))
(check-sat)
