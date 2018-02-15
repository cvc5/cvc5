; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRA)
(set-info :status unsat)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)

(declare-fun a1 () Bool)
(declare-fun a2 () Bool)
(declare-fun a3 () Bool)
(declare-fun a4 () Bool)
(declare-fun a5 () Bool)
(declare-fun a6 () Bool)
(declare-fun a7 () Bool)

(assert (= a2 (and (> (sin 1.0) 0.0) (> (cot 1.0) (/ (cos 1.0) (sin 1.0))))))
(assert (= a7 (> (* (sec 1.0) (cos 1.0)) 1.0)))

(assert (or
a2
a7
))

(check-sat)
