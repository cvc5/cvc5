; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= a (* b (+ (sin a) (/ 1 a)))))
(check-sat)
