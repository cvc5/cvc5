(set-logic LIA)
(set-option :cegqi-nested-qe true)
(set-info :status unsat)
(assert
 (forall ((a Int) (b Int))
 (xor (xor (= a 0) (= b 0))
  (forall ((c Int))
  (= (ite (= a 0) 0 1) (ite (= c 0) 0 1))))))
(check-sat)
