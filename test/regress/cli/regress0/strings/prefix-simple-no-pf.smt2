; COMMAND-LINE: --preregister-mode=lazy
; EXPECT: unsat
(set-logic ALL)
(declare-const x Int)
(declare-const y String)
(assert (str.prefixof "a" (str.substr y 0 x)))
(assert (not (str.prefixof "a" y)))
(check-sat)
