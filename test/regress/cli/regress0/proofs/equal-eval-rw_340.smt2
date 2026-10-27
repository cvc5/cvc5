; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.prefixof "A" (str.from_int 0)) false)))
(check-sat)
(exit)
