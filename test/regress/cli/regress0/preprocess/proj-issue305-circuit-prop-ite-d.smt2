; EXPECT: sat
(set-logic ALL)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (not (ite a b c)))
(assert c)
(assert (not b))
(check-sat)
