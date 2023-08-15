; COMMAND-LINE: --no-fresh-declarations
; EXPECT: sat
(set-logic ALL)
(declare-sort U 0)
(declare-fun y () U)
(declare-fun x () Int)
(declare-fun f (Int) Int)
(assert (> (f x) x))
(assert (= y y))
(check-sat)
