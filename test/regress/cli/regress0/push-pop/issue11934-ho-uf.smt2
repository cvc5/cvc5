; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic HO_ALL)
(declare-fun a (Int Int) Int)
(declare-fun d () Int)
(assert (= (a d 0) (a 0 0)))
(check-sat)
(assert (= d 0))
(check-sat)
