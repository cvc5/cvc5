; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic QF_ALL_SUPPORTED)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun u () Int)
(declare-fun v () Int)
(assert (wand (pto x u) (pto y v)))
(assert (emp 0 0))
(check-sat)
