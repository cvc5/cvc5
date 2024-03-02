; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic QF_NRAT)
(declare-fun x () Real)

(assert (> (exp (- (/ 1 2))) 0.65))
(assert (= x (exp (- (/ 1 2)))))


(check-sat)
