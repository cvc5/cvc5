; EXPECT: unknown
(set-logic ALL)
(assert (forall ((V (Array Int Int))) (= 0 (select V 0))))
(check-sat)
