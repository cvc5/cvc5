; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-fun a (Int) Int)
(declare-fun b (Int) Int)
(assert (= 1 (a (- 1))))
(check-sat)
(assert (= (b 0) ((_ iand 3) 1 (a (- 1)))))
(check-sat)
