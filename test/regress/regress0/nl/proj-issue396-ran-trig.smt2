; COMMAND-LINE: -q
; EXPECT: sat
(set-logic NRAT)
(declare-const x Real)
(declare-const y Real)
(assert (= 0.0 (/ y (- real.pi (+ x (* y x)) (/ 0 (- x y))))))
(check-sat)
