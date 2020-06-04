; COMMAND-LINE: --cegqi-bv --no-cegqi-full
; EXPECT: unsat
(set-logic BV)
(set-info :status unsat)
(assert
   (forall
    ((A (_ BitVec 8)) (B (_ BitVec 8)) (C (_ BitVec 8)) (D (_ BitVec 8)))
      (or (and (= A B) (= C D)) (and (= A C) (= B D)))))

(check-sat)

