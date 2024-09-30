; COMMAND-LINE: -i --solve-real-as-int
; EXPECT: sat
; EXPECT: unknown
(set-logic ALL)
(declare-const a Real) 
(assert (> a 5.0)) 
(check-sat) 
(assert (= a 8.9))
(check-sat) 
