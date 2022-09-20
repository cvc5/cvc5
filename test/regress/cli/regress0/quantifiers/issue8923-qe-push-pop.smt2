; COMMAND-LINE: --incremental
; SCRUBBER: sed 's/(.*)/()/g'
; EXPECT: ()
; EXPECT: ()
; EXIT: 0
(set-logic ALL)

(push)
(declare-const a Int)
(declare-const b Int)
(get-qe (exists ((a Int)) (and (= b 0) (= a 1))))
(pop)

(push)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(get-qe (exists ((y Int)) (and (= x y) (= y z))))
(pop)
