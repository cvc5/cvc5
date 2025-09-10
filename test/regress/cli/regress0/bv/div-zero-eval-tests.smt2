; EXPECT: unsat
(set-logic ALL)

(assert (or

(not (= (bvudiv #b1010 #b0000) #b1111))
(not (= (bvurem #b1010 #b0000) #b1010))

))
(check-sat)
