; EXPECT: sat
; REQUIRES: poly
(set-logic NRA)
(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= (/ 0 (+ 1 (* a a b))) 0))
(check-sat)
