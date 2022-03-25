; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ (str.rev "abc") "d") x))
(assert (= (str.++ (str.to_lower "ABC") (str.toupper "abc")) y))
(check-sat)
