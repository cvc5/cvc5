(set-logic ALL)
(set-option :rels-exp true)
; This is the unsat core that cvc5 extracts from acyclic_union_multi.smt2:
; {(a,b) in R, (b,a) in S, acyclic(tuple R S)}.  Core extraction drops the
; user's self-loop assertion (a,a) in tclosure(R u S) -- the only mention of the
; tclosure term -- so a re-solve of this reduced set has no user-written TC term
; at all.  It must STILL be unsat purely from acyclic(tuple R S): R contributes
; a->b, S contributes b->a, so the union R u S has the cycle a->b->a.
;
; This is the MULTI-RELATION analog of acyclic_union_single.smt2.  Both are
; closed by having acyclic(u) itself register u and its transitive closure
; (lemma acyclic(u) => u <= TC(u)); for the union that registration is what lets
; the set-union up-rule materialize R u S's members so the cycle is derived.
(set-info :status unsat)
(declare-sort Atom 0)
(declare-fun R () (Set (Tuple Atom Atom)))
(declare-fun S () (Set (Tuple Atom Atom)))
(declare-fun a () Atom)
(declare-fun b () Atom)

(assert (set.member (tuple a b) R))            ; a -> b in R
(assert (set.member (tuple b a) S))            ; b -> a in S

(assert (rel.acyclic (tuple R S)))             ; ... yet we claim R u S is acyclic

(check-sat)
