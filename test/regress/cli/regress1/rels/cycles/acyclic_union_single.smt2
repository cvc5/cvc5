(set-logic ALL)
(set-option :rels-exp true)
; Single-relation regression for the term-driven acyclic-down gap.
;
; R has edges a->b and b->a, so R contains a cycle through a, and asserting
; (rel.acyclic (tuple R)) is unsat.  The acyclic-down rule is term-driven: it
; only fires once (rel.tclosure R) is a registered term, so the TC solver builds
; R's closure graph and derives (a,a) in TC(R).  WITHOUT such a term the cycle
; would never be derived and this would wrongly come back sat.
;
; The fix makes acyclic(R) itself register (rel.tclosure R) (via the vacuous
; lemma acyclic(u) => u <= TC(u)), so no user-written tclosure term is needed.
; The commented-out assertion below is the OLD manual workaround that used to be
; required to force registration; it is now redundant.  Expected: unsat.
(set-info :status unsat)
(declare-sort Atom 0)
(declare-fun R () (Set (Tuple Atom Atom)))
(declare-fun a () Atom)
(declare-fun b () Atom)

(assert (set.member (tuple a b) R))        ; a -> b
(assert (set.member (tuple b a) R))        ; b -> a  (so a->b->a is a cycle)

; vacuously true; its only purpose is to register the term (rel.tclosure R)
;; (assert (set.subset R (rel.tclosure R)))

(assert (rel.acyclic (tuple R)))
(check-sat)
