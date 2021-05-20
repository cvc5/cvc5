; COMMAND-LINE: --incremental --no-check-models
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (distinct b 0))
(assert (= b 2))
(assert (= (/ 0 a) 1))
(check-sat)
(assert (= (+ a b) 0))
(check-sat (> b 1))
(check-sat)