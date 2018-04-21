; COMMAND-LINE: --finite-model-find --quant-epr --no-check-models
; EXPECT: sat
(set-logic ALL_SUPPORTED)

(declare-sort Loc 0)
(declare-const l Loc)
(declare-const x Loc)

(assert (wand (pto x x) false))
(assert (forall ((x Loc) (y Loc)) (not (pto x y))))

(check-sat)
