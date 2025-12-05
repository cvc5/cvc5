; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const a Real) 
(assert (> (/ (abs 2) a a) (+ (/ 2 a a) 1.0))) 
(check-sat)        
