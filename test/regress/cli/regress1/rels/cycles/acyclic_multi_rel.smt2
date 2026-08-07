(set-logic ALL)
(set-option :rels-exp true)
; Multi-relation acyclic test via the rewriter union-fold.
; {(1,2)} and {(2,1)} are constant relations, so postRewriteAcyclic unions their
; members ({(1,2),(2,1)}), computes the transitive closure, finds the self-loop
; (1,1)/(2,2), and rewrites (rel.acyclic (tuple ...)) to false.  Expected: unsat.
; Unlike the down-rule version this is resolved entirely in the rewriter, so it
; passes --check-unsat-cores and --check-proofs cleanly.
(set-info :status unsat)

(assert (rel.acyclic (tuple (set.singleton (tuple 1 2)) (set.singleton (tuple 2 1)))))
(check-sat)
