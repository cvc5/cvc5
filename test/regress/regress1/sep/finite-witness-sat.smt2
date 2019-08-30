; COMMAND-LINE: --finite-model-find --quant-epr --no-check-models
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(declare-sort Loc 0)
(declare-const l Loc)

(assert (not (_ emp Loc Loc)))
(assert (forall ((x Loc) (y Loc)) (not (pto x y))))


(check-sat)
