; EXPECT: unsat
(set-logic ALL)
(assert (or

(not (= (str.update "ABC" 0 "") "ABC"))
(not (= (str.update "ABC" 4 "DEF") "ABC"))
(not (= (str.update "ABC" 2 "DEF") "ABD"))
(not (= (str.update "ABC" (- 1) "D") "ABC"))
(not (= (str.update "ABCDEF" 2 "AA") "ABAAEF"))
(not (= (str.update "ABCDEF" 1000 "AA") "ABCDEF"))
(not (= (str.update "ABCDEF" 5 "AA") "ABCDEA"))

(not (= (str.<= "ABC" "A") false))
(not (= (str.<= "" "A") true))
(not (= (str.<= "AAA" "AAAA") true))
(not (= (str.<= "AAB" "AAC") true))
))


(check-sat)
