; COMMAND-LINE: --macros-quant
; EXPECT: unknown
; this will fail if type rule for APPLY_UF requires to be subtypes
(set-logic ALL_SUPPORTED)

(declare-datatypes (T) ((List (cons (hd T) (tl (List T))) (nil))))

(declare-fun R ((List Int)) Bool)
(assert (forall ((x (List Int))) (R x)))
(declare-fun j1 () (List Real))
(assert (not (R j1)))

(declare-fun Q ((Array Real Int)) Bool)
(assert (forall ((x (Array Real Int))) (Q x)))
(declare-fun j2 () (Array Int Real))
(assert (not (Q j2)))

(check-sat)
