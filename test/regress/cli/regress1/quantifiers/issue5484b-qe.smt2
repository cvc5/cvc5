; COMMAND-LINE: -q
; SCRUBBER: sed 's/(.*)/()/g'
; EXPECT: ()
; EXIT: 0
(set-logic NIA)
(declare-fun v0 () Bool)
(declare-fun v1 () Bool)
(declare-fun v2 () Bool)
(declare-fun v3 () Bool)
(declare-fun v4 () Bool)
(declare-fun v7 () Bool)
(declare-fun v8 () Bool)
(declare-fun i6 () Int)
(declare-fun i9 () Int)
(declare-fun i11 () Int)
(declare-fun i13 () Int)
(declare-fun v9 () Bool)
(declare-fun i16 () Int)
(get-qe (forall ((q75 Bool)) (xor (< i9 52) (forall ((q75 Bool)) (not (and (< i16 37) q75 q75 v1))) v2 (and (distinct v4 v3 v4) v9 v9 (and v7 v0 (>= 24 56 i11 i6 7) v0 v8)) (= (+ (div i13 340) 268 i9) i13))))
