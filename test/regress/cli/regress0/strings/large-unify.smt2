; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(assert (or 
(not (=
(=
(str.++ x "abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd") (str.++ y "dabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd"))
(=
(str.++ x "abc") y)
))

(not (=
(=
(str.++ "abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd" x) (str.++ "abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcda" y))
(=
(str.++ "bcd" x) y)
))

))
(check-sat)
