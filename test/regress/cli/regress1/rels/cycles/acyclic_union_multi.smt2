(set-logic ALL)
(set-option :rels-exp true)
; Multi-relation acyclic test (exercises the tuple-of-relations / union path).
; R contributes a->b, S contributes b->a, so the union R∪S has the cycle a->b->a.
; Asserting (rel.acyclic (tuple R S)) then contradicts the materialized self-loop
; (a,a) in tclosure(R∪S) via the acyclic-down rule.  Expected: unsat.
(set-info :status unsat)
(declare-sort Atom 0)
(declare-fun R () (Set (Tuple Atom Atom)))
(declare-fun S () (Set (Tuple Atom Atom)))
(declare-fun a () Atom)
(declare-fun b () Atom)

(assert (set.member (tuple a b) R))            ; a -> b in R
(assert (set.member (tuple b a) S))            ; b -> a in S

; self-loop in the transitive closure of the union -> R∪S has a cycle through a
(assert (set.member (tuple a a) (rel.tclosure (set.union R S))))

; ... yet we claim the union (R, S) is acyclic
(assert (rel.acyclic (tuple R S)))

(check-sat)
