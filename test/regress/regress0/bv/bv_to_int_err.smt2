; COMMAND-LINE: --solve-bv-as-int=1
; EXPECT: (error "Error in option parsing: --solve-bv-as-int=X is only supported for sub-logics of QF_UFBVNIRA.")
; EXIT: 1

(set-logic QF_ALIA)
(declare-fun A () (Array Int Int))
(declare-fun a () Int)
(assert (distinct (* 2 (select A 0)) (+ a 1)))
(check-sat)
