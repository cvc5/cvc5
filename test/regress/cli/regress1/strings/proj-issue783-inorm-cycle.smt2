; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String) 
(declare-fun b () String)  
(assert (not (= (str.replace (str.replace "B" (str.++ (str.replace b "A" b) b) b) 
(str.replace "B" a (str.++ b (str.replace b "A" b))) (str.replace (str.replace "B" a 
(str.replace b "A" b)) a (str.replace (str.replace "B" "B" "A") "A" b))) "B"))) 
(check-sat)        
