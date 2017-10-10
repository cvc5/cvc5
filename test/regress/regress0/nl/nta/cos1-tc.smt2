; COMMAND-LINE: --nl-ext
; EXPECT: unknown
(set-logic UFNRA)
(declare-fun f (Real) Real)

(assert (= (f 0.0) (cos 1)))

(check-sat)
