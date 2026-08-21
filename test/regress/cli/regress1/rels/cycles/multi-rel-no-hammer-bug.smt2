; Regression test for a soundness bug in the relation-acyclicity cycle
; machinery: over a union of >= 2 relations, (not (rel.acyclic (tuple rf po)))
; was accepted with rf/po forming just an acyclic PATH (e.g. c->b->a), not a
; genuine cycle. The cycle-sequence machinery (applySplitCycleLenRule /
; applyUnrollCycle / applyContrMinimalRule in theory_sets_rels.cpp) advances
; its internal cnt one round at a time and is starved/reset by unrelated
; backtracking; meanwhile len(seq) can get pinned to a concrete value by
; completely unrelated string/arithmetic reasoning before the cycle
; machinery's own SplitCycleLen lemma for that exact length is ever
; generated -- so the closing constraint s[0] = s[len-1] is never enforced.
; Fixed by TheorySetsRels::checkAcyclicityLastCall (dispatched via the
; SETS_CHECK_ACYCLICITY_LAST_CALL last-call step), which catches any open
; cycle-sequence obligation up to the model's candidate length for the
; sequence before a candidate model is accepted, forcing a genuine
; conflict if that length's obligation was never actually satisfied.
;
; No self-loops or 2-cycles are allowed in rf u po, so any actual cycle must
; use all three atoms a, b, c (length >= 3). Expected: sat, with rf u po
; containing a genuine 3-cycle.
(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(declare-sort Atom 0)
(declare-fun a () Atom)
(declare-fun b () Atom)
(declare-fun c () Atom)
(declare-fun rf () (Set (Tuple Atom Atom)))
(declare-fun po () (Set (Tuple Atom Atom)))
(assert (distinct a b c))

(define-fun univAtoms () (Set (Tuple Atom))
  (set.union (set.singleton (tuple a))
             (set.union (set.singleton (tuple b)) (set.singleton (tuple c)))))
(define-fun univPairs () (Set (Tuple Atom Atom)) (rel.product univAtoms univAtoms))
(assert (set.subset rf univPairs))
(assert (set.subset po univPairs))

; forbid self-loops in the union rf u po
(assert (not (or (set.member (tuple a a) rf) (set.member (tuple a a) po))))
(assert (not (or (set.member (tuple b b) rf) (set.member (tuple b b) po))))
(assert (not (or (set.member (tuple c c) rf) (set.member (tuple c c) po))))

; forbid 2-cycles in the union rf u po (for every unordered pair of atoms)
(assert (not (and (or (set.member (tuple a b) rf) (set.member (tuple a b) po))
                   (or (set.member (tuple b a) rf) (set.member (tuple b a) po)))))
(assert (not (and (or (set.member (tuple a c) rf) (set.member (tuple a c) po))
                   (or (set.member (tuple c a) rf) (set.member (tuple c a) po)))))
(assert (not (and (or (set.member (tuple b c) rf) (set.member (tuple b c) po))
                   (or (set.member (tuple c b) rf) (set.member (tuple c b) po)))))

; so any cycle in rf u po must have length >= 3, i.e. must use all of a,b,c
(assert (not (rel.acyclic (tuple rf po))))
(check-sat)
