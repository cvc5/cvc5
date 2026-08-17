; r is pinned to the SAME 2-cycle {(a,b),(b,a)} with a != b.
; r is cyclic, so (not (rel.acyclic r)) should be SAT.
; BUG: the fork returns UNSAT -- negated rel.acyclic has no witness support.
(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(set-option :rels-exp true)
(declare-sort A 0)
(declare-fun a () A)
(declare-fun b () A)
(declare-fun r () (Set (Tuple A A)))

(assert (distinct a b))
(assert (= r (set.insert (tuple a b) (set.singleton (tuple b a)))))
(assert (not (rel.acyclic (tuple r))))
(check-sat)
