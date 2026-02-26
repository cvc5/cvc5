; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(assert (not (exists ((a Real)) (forall ((b Real)) 
(exists ((c Real)) (exists ((a Real)) (forall ((b Real)) 
(exists ((c Real)) (and (not (= (+ b c) 0))
(xor (not (= a 0)) (> c 0)))))))))))
(check-sat)                    
