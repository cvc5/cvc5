;; needs --check-models, as --debug-check-models does not trigger the issue
; REQUIRES: poly
; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic QF_NRA)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r10 () Real)
(assert (= r1 (- 0.0 (- 1 r1) (* r2 r2 0.059 (- 1.0)))))
(assert (< 1.0 (+ 34 (- r1) (- 1.0 (- r1) (* r10 r2 r2)))))
(check-sat)
