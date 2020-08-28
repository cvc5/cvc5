; COMMAND-LINE: --nl-ext-tf-tplanes --no-check-models --nl-rlv=always
; EXPECT: sat
(set-logic QF_NRAT)
(set-info :status sat)
(declare-fun x () Real)

(assert (not (= (sin 1.0) 0.5)))
(assert (not (= (sin 1.0) 0.8)))
(assert (not (= (sin 1.0) 0.9)))
(assert (not (= (sin 1.0) (- 0.84))))
(assert (< (- x (sin 1)) 0.000001))
(assert (< (- (sin 1) x) 0.000001))

(check-sat)
