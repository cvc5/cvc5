(set-logic ALL)
(set-option :rels-exp true)
; Minimal non-concrete cycle test. Expected: unsat.
; R has a cycle, but its transitive closure has no self-loop (= R acyclic).
(declare-fun R () (Set (Tuple Int Int)))

; tclosure(R) is irreflexive: no x with (x,x) in tclosure(R)
(assert (forall ((x Int)) (not (set.member (tuple x x) (rel.tclosure R)))))

; ... yet R is not acyclic
(assert (not (rel.acyclic R)))

(check-sat)
