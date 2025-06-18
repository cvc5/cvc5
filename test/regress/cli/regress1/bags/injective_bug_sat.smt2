(set-logic HO_ALL)
(set-info :status sat)
(declare-const E (Bag (Tuple Int)))
(declare-const p (-> (Tuple  Int) Bool))
(declare-const f (-> (Tuple  Int) (Tuple Int Int)))
(assert (= f (lambda ((t (Tuple Int)))
  (tuple
    ((_ tuple.select 0) t)
    6)))
)
(assert
(not (=
  (bag (tuple 0 5) 1)
  (bag.map f (bag.filter p E)))))

(check-sat)
