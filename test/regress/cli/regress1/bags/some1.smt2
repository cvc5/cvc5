(set-logic HO_ALL)
(set-info :status sat)
(declare-const A (Bag Int))
(declare-const B (Bag Int))

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(assert (distinct x y z))

(assert (bag.member x A))
(assert (bag.member y A))
(assert (bag.member z A))

(assert (distinct A (as bag.empty (Bag Int))))

(assert 
  (bag.all 
    (lambda ((a Int)) 
      (bag.some 
        (lambda ((b Int)) (< (* 2 a) b)) 
        B)) 
    A))

(check-sat)
