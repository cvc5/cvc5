; EXPECT: unsat
(set-logic ALL)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))
(assert (or

(not (= (concat y #b0 #b0 #b0 #b0 #b0 #b0 #b0 #b0 x) (concat y #b00000000 x)))
(not (= (concat y ((_ extract 7 7) x) ((_ extract 6 6) x) ((_ extract 5 5) x) ((_ extract 4 4) x) ((_ extract 3 3) x) ((_ extract 2 2) x) ((_ extract 1 1) x) ((_ extract 0 0) x)) (concat y x)))
(not (= (bvxor (bvxor x #b10101010) y z) (bvxor x #b10101010 y z)))

))
(check-sat)
