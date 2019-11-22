; COMMAND-LINE: --uf-ho
; EXPECT: sat
(set-logic ALL)
(declare-fun g (Int) Real)
(declare-fun h (Int) Real)
(assert (not (= g h)))
(assert (= (g 0) 0.0))
(assert (= (h 0) 0.5))
(check-sat)
