(set-logic ALL)
(set-info :status sat)
(declare-const x Int)
(declare-fun v () (Bag Int))
(declare-fun a () String)
(assert 
  (or 
    (= 0 (bag.card v)) 
    (= 
       (str.substr a 1 0) 
       (str.substr (str.from_int 0) (* x x) 1))))
(check-sat)
