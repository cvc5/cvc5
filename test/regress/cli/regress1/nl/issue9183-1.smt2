; EXPECT: sat
(set-logic QF_NRA) 
(set-option :produce-abducts true)
(declare-const a Real) 
(declare-const b Real) 
(assert (> (/ (/ b b) (/ b b)) (/ (/ 1.0 0.0) (/ 1.0 b)))) 
(check-sat)
