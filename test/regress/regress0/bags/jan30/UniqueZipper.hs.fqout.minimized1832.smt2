(set-logic QF_ALL)
(set-info :status unsat)
(define-sort Elt () Int)
(define-sort mySet ()
  (Bag Elt ))
(define-fun smt_set_emp () mySet (as bag.empty mySet))

(declare-fun S () (Bag Int))
(declare-fun T () (Bag Int))
(declare-fun x () Int)

(assert (or (not (= S smt_set_emp)) (>= (bag.count x T) 1)))

(assert (= smt_set_emp 
           (ite (>= (bag.count x T) 1)
                (bag.union_disjoint (bag.union_disjoint smt_set_emp (bag x 1)) S)
                S)))
(check-sat)
