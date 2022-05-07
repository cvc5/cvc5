; SCRUBBER: sed 's/(.*)/()/g'
; EXPECT: ()
; EXIT: 0
(set-logic NIA)
(declare-fun v9 () Bool)
(declare-fun v18 () Bool)
(declare-fun i2 () Int)
(declare-fun v31 () Bool)
(get-qe (forall ((q23 Int) (q24 Int) (q25 Int) (q26 Int) (q27 Bool) (q28 Int) (q29 Int)) (xor (=> (not (not (distinct 83 407))) (> (- i2 31 722) 319)) (forall ((q23 Int) (q24 Int) (q25 Int) (q26 Int) (q27 Bool) (q28 Int) (q29 Int)) (not (not (not v9)))) v31 (> 665 (+ (mod 83 923) (div i2 850)) 319 (- 939 878)) v18)))
