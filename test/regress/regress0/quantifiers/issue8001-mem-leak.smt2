; COMMAND-LINE: -q
; EXPECT: unknown
(assert (forall ((V (Array Int Int))) (= 0 (select V 0))))
(check-sat)
