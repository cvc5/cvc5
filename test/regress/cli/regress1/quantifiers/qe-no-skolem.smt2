; SCRUBBER: sed 's/(.*)/()/g'
; EXPECT: ()
; EXIT: 0
(set-logic ALL)
(declare-const x (_ BitVec 2))
(declare-const y (_ BitVec 2))
(get-qe (exists ((z (_ BitVec 2))) (= (bvmul x z) #b01)))
