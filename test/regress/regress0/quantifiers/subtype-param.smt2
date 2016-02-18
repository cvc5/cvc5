(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-datatypes (T) ((List (cons (hd T) (tl (List T))) (nil))))

(declare-fun R ((List Int)) Bool)
(assert (forall ((x (List Real))) (R x)))

(declare-fun Q ((Array Int Real)) Bool)
(assert (forall ((x (Array Int Int))) (Q x)))

(declare-fun k1 () (List Int))
(declare-fun k2 () (Array Real Int))
(assert (or (not (R k1)) (not (Q k2))))

(check-sat)
