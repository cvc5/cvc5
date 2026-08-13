; EXIT: 1
; DISABLE-TESTER: dump
; EXPECT: (error "Parse Error: issue12572-nullable-lift-no-arguments.smt2:7.34: Function 'f' has type '(-> Int Int)' which expects 1 arguments, but term '(nullable.lift f)' has 0 arguments.")
(set-logic ALL)
(declare-fun z () (Nullable Int))
(declare-fun f (Int) Int)
(assert (= z ((_ nullable.lift f))))
(check-sat)
