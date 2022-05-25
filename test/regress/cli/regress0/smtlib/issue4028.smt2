; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(set-option :incremental true)
(push 3)
(check-sat)
(reset-assertions)
(push 4)
(check-sat)
