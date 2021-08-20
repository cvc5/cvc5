; COMMAND-LINE: --finite-model-find --quant-epr
; EXPECT: sat
(set-logic ALL)
(declare-sort Loc 0)
(declare-const l Loc)
(declare-heap (Loc Loc))

(assert (not (_ emp Loc Loc)))
(assert (forall ((x Loc) (y Loc)) (not (pto x y))))


(check-sat)
