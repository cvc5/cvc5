; EXPECT: sat
; COMMAND-LINE: --sygus-inference --no-check-models --nl-rlv=always
(set-logic ALL)
(declare-fun a () Real)
(assert (> a 0.000001))
(assert (< (- (sin 1) a) 0.000001))
(check-sat)
