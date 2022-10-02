; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic HO_UF)
(set-info :status sat)
(declare-sort U 0)
(declare-fun P (U U) Bool)
(declare-fun Q (U U) Bool)
(declare-fun R (U U) Bool)
(declare-fun a () U)
(declare-fun b () U)

; can solve this using standard MBQI model for P = \ xy true
(assert (forall ((x U) (y U)) (or (P x y) (Q x y))))
(assert (forall ((x U) (y U)) (or (P x y) (R x y))))

(assert (not (= a b)))
(assert (= (Q a) (R b)))
(check-sat)
