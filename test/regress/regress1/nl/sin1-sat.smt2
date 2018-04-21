; COMMAND-LINE: --nl-ext-tf-tplanes --no-check-models
; EXPECT: sat
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun x () Real)

(assert (> (sin 1) 0.84))
(assert (< (sin 1) 0.85))
(assert (< (- x (sin 1)) 0.000001))
(assert (< (- (sin 1) x) 0.000001))

(check-sat)
