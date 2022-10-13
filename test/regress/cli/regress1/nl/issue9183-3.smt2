; COMMAND-LINE: --decision=stoponly --strings-exp
; EXPECT: sat
(set-logic QF_NRA) 
(declare-const a Real) 
(declare-const b Real) 
(assert (> (/ (/ b b) (/ b b)) (/ (/ 0.0 a) b))) 
(check-sat)
