; COMMAND-LINE: --cegqi-bv --cegqi-bv-rm-extract
; EXPECT: sat
(set-logic BV)
(declare-fun k_3 () (_ BitVec 8))
(declare-fun k_4 () (_ BitVec 8))
(declare-fun k_5 () (_ BitVec 8))
(assert 
(forall ((x (_ BitVec 8))) (or (= k_5 x) (not (= k_3 (bvadd (concat #b0000 ((_ extract 7 4) x)) #b01000001))) (not (= k_4 (bvadd (concat #b0000 ((_ extract 3 0) x)) #b01000001)))) ))
(check-sat)
