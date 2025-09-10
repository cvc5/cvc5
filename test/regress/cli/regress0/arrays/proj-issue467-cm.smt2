; EXPECT: sat
(set-logic ALL)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8))) 
(declare-const b (Array (_ BitVec 8) (_ BitVec 8))) 
(declare-const x (_ BitVec 8)) 
(declare-const y (_ BitVec 8)) 
(declare-const z (_ BitVec 4))
(assert (and (= (bvadd #b00000001 (bvneg (select b #b00000000))) x) (= b (store a #b00000001 x))))
(check-sat)
