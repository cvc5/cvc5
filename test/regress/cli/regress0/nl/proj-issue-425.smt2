; COMMAND-LINE: --solve-int-as-bv=5524936381719514648
; EXPECT-ERROR: (error "number of bits provided to `--solve-int-as-bv` should be a uint_32t.")
; STATUS: 1
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (* x x) y))
(check-sat)

