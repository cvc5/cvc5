; COMMAND-LINE: --solve-real-as-int --quiet
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(assert (forall ((x Real) (y Real)) (=> (< x y) (exists ((z Real)) (and (< x z) (< z (+ y 2)))))) )
(check-sat)
