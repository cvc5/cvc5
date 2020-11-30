; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const i7 Int)
(declare-const Str8 String)
(declare-const Str17 String)
(assert (distinct (str.++ "" "rvhhcn" "" Str8 (str.from_int 56)) (str.++ "" (str.from_int i7) "" Str17) Str17))
(check-sat)
