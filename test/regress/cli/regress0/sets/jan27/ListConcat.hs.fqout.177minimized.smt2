(set-logic QF_ALL)
(set-info :status unsat)
(define-sort Elt () Int)
(define-sort mySet () (Set Elt ))
(define-fun smt_set_emp () mySet (as set.empty mySet))

(declare-fun S () (Set Int))
(declare-fun T () (Set Int))

(assert (not (= S T)))
(assert (= T (set.union smt_set_emp S)))
(check-sat)

; What was the bug?
;
; When two sets were disequal, the corresponding lemma
; was not being generated (stating there in an element
; in one, but not in the other).
