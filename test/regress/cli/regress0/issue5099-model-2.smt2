; COMMAND-LINE: -m
; EXPECT: sat
; EXPECT: ((IP true))
(set-logic QF_NRA)
(declare-const r11 Real)
(declare-const r16 Real)
(assert (! (distinct (/ 1 r16) r11) :named IP))
(check-sat)
(get-assignment)
