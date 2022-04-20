; EXPECT: sat
; DISABLE-TESTER: model
(set-logic QF_ALL)
(set-info :status sat)
(declare-fun x () Int)
(declare-heap (Int Int))

(assert (sep (= x 0) (not (= x 5))))

(declare-fun y () Int)
(assert (pto y 0))
(check-sat)
