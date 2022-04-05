(set-logic ALL)
(set-info :status unsat)
(set-option :fmf-bound true)
(declare-fun B () (Bag (Tuple Int Int)))
(declare-fun x () (Tuple Int Int))
(assert
 (and (= (as bag.empty (Bag (Tuple Int Int))) (bag x (bag.card B)))
      (not (= (as bag.empty (Bag (Tuple Int Int))) B))))
(check-sat)
