; SCRUBBER: sed 's/(.*)/()/g'
; EXPECT: ()
; EXIT: 0
(set-logic LIA)
(declare-fun a () Int)
(get-qe (exists ((b Int)) (= a 0)))
