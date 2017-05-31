(set-logic BV)
(set-info :status unsat)
(assert
   (forall
    ((A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)))
      (or (and (= A B) (= C D)) (and (= A C) (= B D)))))
      
(check-sat)
      
