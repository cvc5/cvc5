; COMMAND-LINE: -o learned-lits
; SCRUBBER: grep -v -E '(\(learned-lit)'
; EXPECT: sat
(set-logic ALL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 0))
(assert (or (< x 0) (> y 0)))
(check-sat)
