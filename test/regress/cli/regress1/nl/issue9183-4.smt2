; COMMAND-LINE: --sygus-inst
; EXPECT: sat
(set-logic QF_NRA) 
(declare-const a Real) 
(declare-const b Real) 
(assert (> 1.0 (/ (/ b a) (/ 0.0 b)))) 
(check-sat)
