; COMMAND-LINE: --cegqi --decision=internal
; EXPECT: unsat
(set-logic LIA)
(set-info :status unsat)

(assert (or 
(forall ((H Int) (G Int)) (= (= G 0) (= H 0)))

(forall ((C Int) (D Int) (E Int)) (or 
(= (= D 0) (= C 0)) 
(and 
(not (forall ((G Int)) (= (= E 0) (= G 0)))) 
(not (forall ((A Int)) 
  (not (= (ite (= A 0) 0 1) (ite (= C 0) 0 2)))
))
)))
))

(check-sat)
