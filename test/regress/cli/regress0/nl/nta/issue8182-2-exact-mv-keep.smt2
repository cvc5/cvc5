; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= a (* b (+ (sin a) (/ 1.0 a)))))
(check-sat)
