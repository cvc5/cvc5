; DISABLE-TESTER: dump
; SCRUBBER: grep -o '(error "Parse Error: issue9676.smt2:6.12: expected 3 arguments'
; EXPECT: (error "Parse Error: issue9676.smt2:6.12: expected 3 arguments
; EXIT: 1
(set-logic ALL)
(assert (fp))
