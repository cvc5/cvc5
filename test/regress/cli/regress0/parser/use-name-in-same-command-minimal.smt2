; EXPECT: sat
(set-logic ALL)
(declare-fun a () Int)
(assert (= (! a :named n) n))
(check-sat)