; REQUIRES: unrestricted-mode
; COMMAND-LINE: --proof-check=eager
; EXPECT: unsat
;
; Reduced from issue #12810. Requires a tangent plane for exp at 2, whose
; approximation degree must be increased for the proof step to be valid.
(set-logic ALL)
(declare-const S Real)
(assert (and (= S 2) (= 0.0 (/ 1.0 (to_real (to_int (exp S)))))))
(check-sat)
