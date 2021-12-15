; COMMAND-LINE: --nl-ext=full --no-nl-ext-tf-tplanes --no-nl-ext-inc-prec
; EXPECT: sat
(set-logic UFNRAT)
(declare-fun f (Real) Real)

(assert (= (f 0.0) (cos 1)))

(check-sat)
