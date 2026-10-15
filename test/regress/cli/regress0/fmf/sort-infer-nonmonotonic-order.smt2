; COMMAND-LINE: --finite-model-find --sort-inference
; EXPECT: unsat
; The quantified formula Q occurs negatively before it occurs positively. The
; monotonicity check must still see the variables of Q in the ITE terms.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun c () U)
(declare-fun a () U)
(declare-fun p (U) Bool)
(declare-fun q (U U) Bool)
(define-fun Q () Bool (forall ((X U) (Y U)) (= (ite (q X Y) X Y) (ite (q X Y) Y X))))
(assert (or (not Q) (p a)))
(assert Q)
(assert (forall ((X U) (Y U)) (q X Y)))
(assert (forall ((X U)) (not (= (f X) c))))
(check-sat)
