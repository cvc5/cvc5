(set-logic QF_ALL_SUPPORTED)
(set-info :status unsat)
(define-sort Elt () Int)
(define-sort mySet ()
  (Set Elt ))
(define-fun smt_set_emp () mySet (as emptyset mySet))

(declare-fun S () (Set Int))
(declare-fun T () (Set Int))
(declare-fun x () Int)

(assert (or (not (= S smt_set_emp)) (member x T)))

(assert (= smt_set_emp 
           (ite (member x T) 
                (union (union smt_set_emp (singleton x)) S) 
                S)))
(check-sat)
