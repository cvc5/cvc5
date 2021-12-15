(set-logic QF_ALL)
(set-info :status unsat)
(define-sort Elt () Int)
(define-sort mySet () (Bag Elt ))
(define-fun smt_set_emp () mySet (as bag.empty mySet))

(declare-fun S () (Bag Int))
(declare-fun T () (Bag Int))

(assert (not (= S T)))
(assert (= T (bag.union_disjoint smt_set_emp S)))
(check-sat)

; What was the bug?
;
; When two sets were disequal, the corresponding lemma
; was not being generated (stating there in an element
; in one, but not in the other).
