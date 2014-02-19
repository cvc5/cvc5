; COMMAND-LINE: --rewrite-divk
; EXPECT: unknown
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (= (+ (* z 2) 1) (* x y)))
(check-sat)
(exit)
