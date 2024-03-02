; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic QF_NRAT)
(set-info :status unsat)
(declare-fun x () Real)

(assert (< (exp 1) 2.717))
(assert (= x (exp 1)))


(check-sat)
