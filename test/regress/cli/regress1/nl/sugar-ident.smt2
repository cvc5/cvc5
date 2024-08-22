; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)

(declare-fun a1 () Bool)
(declare-fun a3 () Bool)
(declare-fun a4 () Bool)
(declare-fun a5 () Bool)
(declare-fun a6 () Bool)

(assert (= a1 (and (<= (- 1) x1 1) (not (= (sin (arcsin x1)) x1)))))
(assert (= a3 (and (<= (- 1) x3 1) (< (arccos x3) 0))))
(assert (= a4 (> (arctan x4) 1.8)))

(assert (or a1 a3 a4))

(check-sat)
