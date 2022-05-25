(set-logic ALL)
(set-info :status sat)
(declare-fun a () (Table Int Int))
(declare-fun b () (Table Int Int))
(declare-fun c () Int) ; c here is zero
(assert
  (and
    (= b (bag.difference_subtract b a)) ; b is empty
    (= a (bag (tuple c 0) 1)))) ; a = {|(<0, 0>, 1)|}
(check-sat)
