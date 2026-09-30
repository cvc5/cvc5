; COMMAND-LINE: --rels-acyclic-hammer --rels-acyclic-unroll-max=3
; EXPECT: unsat
;
; Companion to unroll-max-catchup-sat.smt2: same pinned 4-cycle r, but this
; time directly asserting (rel.acyclic (tuple r)) as well, which is
; immediately contradictory given r's concrete membership -- no
; cycle-witnessing machinery is needed to detect the conflict at all.
; Confirms --rels-acyclic-unroll-max does not interfere with straightforward,
; already-grounded acyclicity conflicts.
(set-logic ALL)
(set-info :status unsat)
(declare-sort Atom 0)
(declare-fun a () Atom)
(declare-fun b () Atom)
(declare-fun c () Atom)
(declare-fun d () Atom)
(declare-fun r () (Set (Tuple Atom Atom)))

(assert (distinct a b c d))
(assert (= r (set.union (set.singleton (tuple a b))
             (set.union (set.singleton (tuple b c))
             (set.union (set.singleton (tuple c d))
                        (set.singleton (tuple d a)))))))
(assert (rel.acyclic (tuple r)))
(check-sat)
