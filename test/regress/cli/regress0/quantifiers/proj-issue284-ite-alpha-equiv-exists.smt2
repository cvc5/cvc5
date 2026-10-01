; EXPECT: sat
(set-logic ALL)
(assert (ite (not (exists ((x Int)) (= "-" (str.substr "-" x (- 1 x))))) true (exists ((x Int)) (= "-" (str.substr "-" x (- 1 x))))))
(check-sat)
