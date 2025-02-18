; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(assert (= "AFBCDEFG" (str.++ x "C" y "F" z "E" w "G")))
(check-sat)
