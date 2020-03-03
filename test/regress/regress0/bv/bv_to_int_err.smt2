; COMMAND-LINE: --solve-bv-as-int=1
; EXPECT: (error "Error in option parsing: --solve-bv-as-int=X only supported for QF_BV and QF_UFBV.")
; EXIT: 1

(set-logic QF_LIA)
(declare-fun a () Int)
(assert (distinct (* 2 a) (+ a 1)))
(check-sat)
