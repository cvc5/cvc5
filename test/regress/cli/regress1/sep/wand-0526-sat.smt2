; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_ALL)
(declare-heap (Int Int))
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun u () Int)
(declare-fun v () Int)
(assert (wand (pto x u) (pto y v)))
(assert sep.emp)
(check-sat)
