; COMMAND-LINE: -o subs
; EXPECT: (substitution (= a 3))
; EXPECT: sat
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= (* 2 a) 6))
(assert (> b a))
(check-sat)
