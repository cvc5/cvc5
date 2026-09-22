; COMMAND-LINE: --decision=internal
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(assert (distinct (str.replace x (str.at x 0) "") (str.substr x 1 (str.len x))))
(check-sat)
