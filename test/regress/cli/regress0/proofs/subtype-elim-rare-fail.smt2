; COMMAND-LINE: --proof-elim-subtypes
; EXPECT: unsat
(set-logic LRA)
(declare-const b Real)
(assert (< (+ 3.0 b) (+ b 2.0)))
(assert (not false))
(check-sat)
