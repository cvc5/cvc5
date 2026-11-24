; EXPECT: (error "Parse Error: tuple-tester.smt2:7.24: Symbol 'tuple' not declared as a variable")
; EXIT: 1
; DISABLE-TESTER: dump
;; Testers of tuples are not supported.
(set-logic ALL)
(declare-const u (Tuple Int))
(assert ((_ is tuple) u))
(check-sat)
