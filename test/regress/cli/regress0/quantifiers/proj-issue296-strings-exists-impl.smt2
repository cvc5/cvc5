; EXPECT: sat
(set-logic ALL)
(set-option :strings-exp true)
(declare-const x Bool)
(declare-const c String)
(assert (=> x (exists ((x Int)) (= c (str.substr c x x))) (exists ((x Int)) (= c (str.substr c x x)))))
(check-sat)
