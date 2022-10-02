; EXPECT: sat
(set-logic HO_ALL)
(declare-fun g (Int) Real)
(declare-fun h (Int) Real)
(assert (not (= g h)))
; g will be given a model value of lambda x. 0.0, which is interpreted as
; a function Int -> Int; however since function types T -> U are subtypes of
; T -> U' where U is a subtype of U', this example works.
(assert (= (g 0) 0.0))
(assert (= (h 0) 0.5))
(check-sat)
