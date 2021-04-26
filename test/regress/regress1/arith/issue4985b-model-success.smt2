; COMMAND-LINE:
; EXPECT: sat
(set-logic QF_AUFNRA)
(set-info :status sat)
(declare-const a (Array Real Real))
(declare-const r Real)
(assert (= 1.0 (select a (/ 2 r))))
(check-sat)
