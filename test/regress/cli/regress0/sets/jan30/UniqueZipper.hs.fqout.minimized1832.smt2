(set-logic QF_ALL)
(set-info :status unsat)
(define-sort Elt () Int)
(define-sort mySet ()
  (Set Elt ))
(define-fun smt_set_emp () mySet (as set.empty mySet))

(declare-fun S () (Set Int))
(declare-fun T () (Set Int))
(declare-fun x () Int)

(assert (or (not (= S smt_set_emp)) (set.member x T)))

(assert (= smt_set_emp 
           (ite (set.member x T) 
                (set.union (set.union smt_set_emp (set.singleton x)) S) 
                S)))
(check-sat)
