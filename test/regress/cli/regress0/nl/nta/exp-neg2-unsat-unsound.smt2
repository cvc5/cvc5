; COMMAND-LINE: --nl-ext-tf-tplanes -q
; EXPECT: sat
(set-logic QF_NRAT)
(declare-fun x () Real)
(assert (or 
(and (<= (exp x) 0.01) (= x (- 2.0)))
(and (> (exp x) 0.2) (= x (- 1.0)))
)
)
(check-sat)
