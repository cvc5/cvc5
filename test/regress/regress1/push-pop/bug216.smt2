; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat

(set-logic QF_UF)
(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (=> x y))
(check-sat) ; returns sat
(assert (=> y x))
(assert (and x (not y)))
(check-sat) ; returns sat --> ERROR
