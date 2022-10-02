; COMMAND-LINE: --miplib-trick
; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun tmp1 () Int)
(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (=> (and (not x) (and (not y) true)) (= tmp1 0)))
(assert (=> (and x (and (not y) true)) (= tmp1 4)))
(assert (=> (and (not x) (and y true)) (= tmp1 6)))
(assert (=> (and x (and y true)) (= tmp1 12)))
(assert (> tmp1 10))
(check-sat)
