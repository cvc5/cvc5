; COMMAND-LINE: -o learned-lits
; SCRUBBER: sed -e 's/(learned-lit.*/learned-lit/'
; EXPECT: learned-lit
; EXPECT: learned-lit
; EXPECT: learned-lit
; EXPECT: sat
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 10))
(assert (or (< x 5) (> y 0)))
(check-sat)
