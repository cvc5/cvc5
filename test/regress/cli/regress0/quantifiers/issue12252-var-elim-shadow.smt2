; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(assert (forall ((a Bool) (b Bool))                                          
(= (=> false true) (exists ((c Bool))                                                              
(and (=> a (or (and (= c b) (forall ((b Bool))                           
(and (= c (and a b))))))))))))                  
(check-sat)     
