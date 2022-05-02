(set-logic ALL)
(set-info :status sat)
(declare-sort U 0)
(declare-fun x () U)
(declare-fun y () U)
(declare-fun z () U)
(declare-fun w () U)
(declare-fun u () U)
(declare-fun v () U)
(declare-fun a () U)
(declare-fun P (U) Bool)

(assert (distinct w u v a))
(assert (or (= x y) (= x z) (= y z)))
(assert (or (P x) (P y) (P z) (P w)))

; should get { x, y, z }, { w }, { u, v, a }
(check-sat)

