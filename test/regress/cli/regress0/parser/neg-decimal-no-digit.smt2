; EXPECT: (error "Parse Error: neg-decimal-no-digit.smt2:8.14: Symbol '-.5' not declared as a variable")
; EXIT: 1
; DISABLE-TESTER: dump
; REQUIRES: no-competition
(set-logic ALL)
(declare-const x Real)
(assert (= x -1.5))
(assert (= x -.5))
(check-sat)
