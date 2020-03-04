; COMMAND-LINE: --solve-bv-as-int=1
; EXPECT: (error "Error in option parsing: --solve-bv-as-int=X only supported for QF_BV and QF_UFBV.")
; EXIT: 1

(set-logic QF_ALIA)
(declare-fun A () (Array Int Int))
(declare-fun a () Int)
(assert (distinct (* 2 (select A 0)) (+ a 1)))
(check-sat)
