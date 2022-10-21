; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(declare-const a (Array (_ BitVec 64) (_ BitVec 64))) 
(declare-const b (_ BitVec 64)) 
(assert (= (store a (select a b) (bvor b b)) (store (store a b b) 
        (select a #x1111111111111111) (bvadd b #x1111111111111111)))) 
(check-sat)
