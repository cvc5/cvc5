; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Int)                                                             
(declare-fun b () Int)                                                             
(assert (> b 0))                                                                   
(assert (not (= (/ (* a b) b) a)))                                                 
(check-sat)  
