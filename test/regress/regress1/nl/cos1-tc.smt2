; COMMAND-LINE: --nl-ext --no-nl-ext-tf-inc-prec
; EXPECT: unknown
(set-logic UFNRA)
(declare-fun f (Real) Real)

(assert (= (f 0.0) (cos 1)))

(check-sat)
