; EXPECT: true
; EXPECT: real.pi
(set-logic ALL)
(declare-fun x () Int)
(rewrite (= x x))
(rewrite real.pi)
