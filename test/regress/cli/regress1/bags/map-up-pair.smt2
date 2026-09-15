; Two rows that agree on the projected column give that column's value a
; multiplicity of two, so the projection cannot be a set. Needs the pairwise
; lower bound: mapUp1 alone only gives a multiplicity of one.
(set-logic HO_ALL)
(set-info :status unsat)
(set-option :bags-map-up-pair true)
(declare-fun T () (Table Int Int))
(assert (> (bag.count (tuple 1 10) T) 0))
(assert (> (bag.count (tuple 1 20) T) 0))
(assert (= (bag.setof ((_ table.project 0) T)) ((_ table.project 0) T)))
(check-sat)
