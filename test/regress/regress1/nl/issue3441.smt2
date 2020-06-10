; COMMAND-LINE: --quiet
; EXPECT: sat
(set-logic QF_NIA)   
(set-info :status sat)                                                           
(declare-fun a () Int)                                                          
(declare-fun b () Int)                                                          
(declare-fun c () Int)                                                          
(declare-fun d () Int)                                                          
(assert (and (>= (+ (* b c (- (-  4) d)) (- 1)) 0 (div a b))))                  
(check-sat)  
