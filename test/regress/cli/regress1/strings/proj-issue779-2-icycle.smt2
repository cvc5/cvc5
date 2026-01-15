; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)                                                          
(declare-fun y () String)                                                          
(declare-fun z () Int)                                                             
(assert (not (= (xor (not (= (str.suffixof "A" (str.replace x "A" "")) 
(str.suffixof "A" (str.replace x "A" "B")))) 
(str.suffixof "A" (str.replace x "A" "B"))) (str.suffixof "A" (str.replace 
(str.++ (str.replace x "A" 
(str.replace "B" (str.replace x (str.replace_all (str.replace x "A" "B") 
(str.replace x "A" "B") x) "") "A")) 
(str.replace x "A" (str.replace "B" (str.replace x (str.replace_all (str.replace x "A" "B") 
(str.replace x "A" "B") x) "") "A"))) (str.replace "B" "B" "") "B")))))                             
(check-sat)                                                                     
(exit)      
