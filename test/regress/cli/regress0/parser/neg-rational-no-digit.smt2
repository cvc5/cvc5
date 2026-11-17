; EXPECT: (error "Parse Error: neg-rational-no-digit.smt2:6.14: Symbol '-/5' not declared as a variable")
; EXIT: 1
; DISABLE-TESTER: dump
(set-logic ALL)
(declare-const x Real)
(assert (= x -/5))
(check-sat)
