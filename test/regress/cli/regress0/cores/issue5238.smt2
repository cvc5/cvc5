; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (distinct b 0.0))
(assert (= b 2.0))
(assert (= (/ 0.0 a) 1.0))
(check-sat)
(assert (= (+ a b) 0.0))
(check-sat-assuming ((> b 1.0)))
(check-sat)
