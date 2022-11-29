(set-logic ALL)
(set-info :status unsat)
(set-option :fmf-bound true)
(declare-fun B () (Table Int Int))
(declare-fun x () (Tuple Int Int))
(assert
 (and (= (as bag.empty (Table Int Int)) (bag x (bag.card B)))
      (not (= (as bag.empty (Table Int Int)) B))))
(check-sat)
