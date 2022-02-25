; COMMAND-LINE: --simplification=none
; EXPECT: unknown
(set-logic ALL)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (and (= a 0) (= b (cos a))))

; currently returns unknown since reductions for sine don't track model values for boundary points, e.g. k = pi/2
(check-sat)
