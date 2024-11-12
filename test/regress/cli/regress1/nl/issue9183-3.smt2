; COMMAND-LINE: --decision=stoponly
; EXPECT: sat
(set-logic QF_NRA) 
(declare-const a Real) 
(declare-const b Real) 
(assert (> (/ (/ b b) (/ b b)) (/ (/ 0.0 a) b))) 
(check-sat)
