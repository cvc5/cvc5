; EXPECT: sat
(set-logic BV)
(set-info :status sat)
(declare-fun k_141 () (_ BitVec 16))
(declare-fun k_140 () (_ BitVec 1))
(declare-fun k_139 () (_ BitVec 16))
(assert
(forall ((x (_ BitVec 2)) (y (_ BitVec 2))) 
(= (bvadd (bvneg (concat #b0 x)) (bvadd (bvneg (concat #b0 y)) (concat (bvor (bvand ((_ extract 1 1) x) ((_ extract 1 1) y)) (bvor (bvand ((_ extract 0 0) x) (bvand ((_ extract 0 0) y) ((_ extract 1 1) y))) (bvand ((_ extract 0 0) x) (bvand ((_ extract 0 0) y) ((_ extract 1 1) x))))) (concat ((_ extract 0 0) (bvlshr k_141 (concat #b0000000000000 (concat ((_ extract 1 1) x) (concat ((_ extract 1 1) y) (bvand ((_ extract 0 0) x) (bvand ((_ extract 0 0) y) (bvnot k_140)))))))) ((_ extract 0 0) (bvlshr k_139 (concat #b0000000000000 (concat ((_ extract 0 0) x) (concat ((_ extract 0 0) y) #b0))))))))) #b000) )
)
(check-sat)
