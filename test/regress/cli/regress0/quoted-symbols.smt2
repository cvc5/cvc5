; EXPECT: sat
(set-logic ALL)
(declare-fun x () Int)
(assert (= |x| 0))
(declare-fun |y| () Int)
(assert (= y 0))
(assert (= (|str.len| "ABC") 3))
(assert (= ((_ |extract| 3 0) #b010101) #b0101)) 
(check-sat)
