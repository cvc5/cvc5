; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(declare-fun x () Real)

(assert (< (exp (- (/ 1 2))) 0.6))
(assert (= x (exp (- (/ 1 2)))))


(check-sat)
