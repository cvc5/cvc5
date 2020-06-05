; EXPECT: sat
; COMMAND-LINE: --sygus-inference
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (xor (> a 0) (not (and (ite (= a b) (> (* 4 a b) 1) true) (> (* a a) 0)))))
(assert (= a b))
(assert (> (* a b) 0))
(check-sat)

