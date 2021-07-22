; COMMAND-LINE:
; EXPECT: sat
(set-logic QF_AUFNRA)
(set-info :status sat)
(declare-const arr0 (Array Real Real))
(declare-const r5 Real)
(declare-const r19 Real)
(assert (! (<= 0.0 0.0 48107.0 (- 6.7954749 0.0 6.7954749 0.0 (select arr0 (/ 40.87941 r5))) r19) :named IP_174))
(check-sat)
