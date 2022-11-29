; COMMAND-LINE: --produce-interpolants
; EXPECT: sat
(set-logic QF_NRA) 
(declare-const a Real) 
(declare-const b Real) 
(assert (> (/ (/ b b) (/ b b)) (/ b (/ b b)))) 
(check-sat)
