; COMMAND-LINE: --nl-ext --no-nl-ext-tf-inc-taylor-deg
; EXPECT: unknown
(set-logic UFNRA)
(declare-fun f (Real) Real)

(assert (= (f 0.0) (cos 1)))

(check-sat)
