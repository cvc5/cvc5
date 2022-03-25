; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
(set-logic QF_LRA)
(set-option :incremental true)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (< c 0))
(assert (> (+ a b) 0))
(assert (or (< a 1) (> c 1)))
(check-sat)
(assert (= b (- 1)))
(check-sat-assuming (true))
(check-sat)
