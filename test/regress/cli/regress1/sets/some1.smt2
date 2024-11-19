(set-logic HO_ALL)
(set-info :status sat)
(declare-const A (Set Int))
(declare-const B (Set Int))

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(assert (distinct x y z))

(assert (set.member x A))
(assert (set.member y A))
(assert (set.member z A))

(assert (not (set.is_empty A)))

(assert 
  (set.all 
    (lambda ((a Int)) 
      (set.some 
        (lambda ((b Int)) (< (* 2 a) b)) 
        B)) 
    A))

(check-sat)
