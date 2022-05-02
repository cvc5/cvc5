; COMMAND-LINE: --force-logic QF_LIRA
; EXPECT: sat
; EXPECT: sat

; Intentionally set the wrong logic
(set-logic QF_BV)
(declare-const x Real)
(assert (= x (- 2.5)))
(check-sat)

(reset)

; Intentionally set the wrong logic
(set-logic QF_BV)
(declare-const x Int)
(assert (= x 2))
(check-sat)
