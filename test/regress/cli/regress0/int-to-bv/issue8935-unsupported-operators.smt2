; EXPECT: (error "Cannot translate the operator str.to_int to a bit-vector operator. Remove option `--solve-int-as-bv`.")
; EXIT: 1
(set-option :solve-int-as-bv 1)
(set-logic ALL)
(declare-fun a () String)
(assert (ite (= (- 1) (str.to_int a)) false true))
(check-sat)
