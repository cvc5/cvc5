; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_ALL)
(set-info :status sat)
(declare-sort U 0)
(declare-heap (U U))
(declare-fun x () U)
(declare-fun y () U)
(declare-fun a () U)
(declare-fun b () U)

(assert (not (sep (not (pto x a)) (pto y b))))
(check-sat)
