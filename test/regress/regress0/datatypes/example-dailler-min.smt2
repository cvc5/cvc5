; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-datatypes ((D 0)) (((C (R Bool)))))
(declare-fun a () (Array Int D))
(declare-fun P ((Array Int D)) Bool)
(assert (P a))
(check-sat)
