; COMMAND-LINE: --nl-ext-tplanes
; EXPECT: sat
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (< x 0))
(assert (= (* x x) 16))
(assert (= x y))
(assert (> ((_ iand 4) x y) 0))
(check-sat)
