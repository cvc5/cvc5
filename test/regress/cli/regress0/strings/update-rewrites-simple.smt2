; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(assert (or
(not (= (str.update (str.++ "ABC" x) 1 "A") (str.++ "AAC" x)))
(not (= (str.update "ABCE" 2 (str.++ "DDD" x)) "ABDD"))
)
)
(check-sat)
