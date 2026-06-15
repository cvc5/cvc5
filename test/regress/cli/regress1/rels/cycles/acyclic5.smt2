(set-logic ALL)
(set-option :rels-exp true)
; Minimal non-concrete cycle test. Expected: unsat.
; R has a cycle, but its transitive closure has no self-loop (= R acyclic).
(declare-sort Atom 0)
(declare-fun R () (Set (Tuple Atom Atom)))
(declare-fun a () (Tuple Atom Atom))
(declare-fun b () (Tuple Atom Atom))
(declare-fun c () (Tuple Atom Atom))

; tclosure(R) is irreflexive: no x with (x,x) in tclosure(R)
(assert (forall ((x Atom)) (not (set.member (tuple x x) (rel.tclosure R)))))

; ... yet R is not acyclic
(assert (not (rel.acyclic R)))

(assert (= R (set.insert a c (set.singleton b))))

(check-sat)
