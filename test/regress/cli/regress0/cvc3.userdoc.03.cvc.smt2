; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun bv () (_ BitVec 10))
(declare-fun a () Bool)
(check-sat-assuming ( (not (and (= ((_ extract 5 3) #b01100000) ((_ extract 4 2) (concat #b1111001 ((_ extract 0 0) bv)))) (= (concat #b1 (ite a #b0 #b1)) ((_ extract 1 0) (ite a #b110 #b011))))) ))
