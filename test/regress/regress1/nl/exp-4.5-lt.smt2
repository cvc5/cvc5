; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRA)
(declare-fun x () Real)

(assert (> (exp x) 2000.0))
(assert (< x 4.5))

(check-sat)
