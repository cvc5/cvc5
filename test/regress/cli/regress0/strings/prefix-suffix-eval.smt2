; EXPECT: unsat
(set-logic ALL)

(assert (or

(not (= (str.prefixof "AB" "ABC") true))
(not (= (str.prefixof "ABC" "AB") false))
(not (= (str.prefixof "ABC" "") false))
(not (= (str.suffixof "BC" "ABC") true))
(not (= (str.suffixof "ABC" "BC") false))
(not (= (str.suffixof "ABC" "") false))

))
(check-sat)
