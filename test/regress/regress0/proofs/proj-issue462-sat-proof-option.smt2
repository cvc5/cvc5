; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :global-declarations true)
(set-option :proof-mode sat-proof)
(declare-const _x3 Int)
(assert (>= (str.to_code (str.from_code _x3)) _x3))
(check-sat)
