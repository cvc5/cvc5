; REQUIRES: unrestricted-mode
; COMMAND-LINE: --finite-model-find --sort-inference
; EXPECT: unsat
; The equality between ITE terms forces U to be a singleton, so U is not
; monotonic even though no variable occurs directly in an equality.
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun c () U)
(declare-fun q (U U) Bool)
(assert (forall ((X U) (Y U)) (q X Y)))
(assert (forall ((X U) (Y U)) (= (ite (q X Y) X Y) (ite (q X Y) Y X))))
(assert (forall ((X U)) (not (= (f X) c))))
(check-sat)
