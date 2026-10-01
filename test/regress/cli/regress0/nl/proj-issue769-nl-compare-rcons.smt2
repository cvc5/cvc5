; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (> a 0)) 
(assert (> b 0)) 
(assert (not (= (/ (* a b) (abs b)) a))) 
(check-sat)     
