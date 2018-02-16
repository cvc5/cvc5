; EXIT: 1
; EXPECT: (error "Parse Error: errorcrash.smt2:5.29: Symbol 'Array' not declared as a type")
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x () (Array U U))
(declare-fun y () (Array U U))
(assert (= x y))
(check-sat)
(get-value (x y))
