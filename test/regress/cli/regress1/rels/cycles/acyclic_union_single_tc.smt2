(set-logic ALL)
(set-option :rels-exp true)
; Single-relation acyclic test where the user ALSO supplies a tclosure term.
;
; R has edges a->b and b->a, so R contains a cycle through a, and asserting
; (rel.acyclic (tuple R)) is unsat.  acyclic_union_single.smt2 is the same
; problem with no tclosure term, relying on the fix to register one; here the
; user additionally asserts (set.subset R (rel.tclosure R)) -- logically vacuous
; (it holds for every relation) but it independently registers (rel.tclosure R).
; This pins down that the acyclic constraint and a user-written tclosure term
; coexist correctly (the cycle is still derived, no double-registration issue).
; Expected: unsat.
(set-info :status unsat)
(declare-sort Atom 0)
(declare-fun R () (Set (Tuple Atom Atom)))
(declare-fun a () Atom)
(declare-fun b () Atom)

(assert (set.member (tuple a b) R))        ; a -> b
(assert (set.member (tuple b a) R))        ; b -> a  (so a->b->a is a cycle)

; vacuously true; its only purpose is to register the term (rel.tclosure R)
(assert (set.subset R (rel.tclosure R)))

(assert (rel.acyclic (tuple R)))
(check-sat)
