; COMMAND-LINE: --cegqi-nested-qe -q
; EXPECT: sat
(set-logic BV)
(set-option :cegqi-nested-qe true)
(set-info :status sat)
(assert
 (exists ((a (_ BitVec 32)))
 (forall ((b (_ BitVec 32)) (c (_ BitVec 32)))
  (exists ((d (_ BitVec 32)) (e (_ BitVec 32)))
  (forall ((g (_ BitVec 32)))
   (exists ((f (_ BitVec 32)))
   (=> (= (_ bv0 32) a)
    (= (bvadd e g) (bvand d f) b c))))))))
(check-sat)
