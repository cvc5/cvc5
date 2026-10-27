; REQUIRES: unrestricted-mode
; COMMAND-LINE: --finite-model-find --sort-inference
; EXPECT: unsat
; Based on TPTP GRA121+1, which cvc5 1.3.4 wrongly reported satisfiable with
; these options. The injective f with c not in its range forces an infinite
; domain, so there is no model of size at most 3.
(set-logic UFC)
(declare-sort U 0)
(declare-fun r (U U) Bool)
(declare-fun f (U) U)
(declare-fun c () U)
(assert (forall ((X U) (Y U)) (or (not (r X Y)) (r Y X))))
(assert (forall ((X U) (Y U) (Z U)) (or (= X Y) (= X Z) (= Y Z) (not (r X Y)) (not (r X Z)) (not (r Y Z)))))
(assert (forall ((X U) (Y U) (Z U) (W U)) (or (= X Y) (= X Z) (= Y Z) (= X W) (= Y W) (= Z W) (r X Y) (r X Z) (r Y Z) (r X W) (r Y W) (r Z W))))
(assert (forall ((X U)) (not (= (f X) c))))
(assert (forall ((X U) (Y U)) (or (not (= (f X) (f Y))) (= X Y))))
(assert (_ fmf.card U 3))
(check-sat)
