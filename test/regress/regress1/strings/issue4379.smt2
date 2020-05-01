; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const i7 Int)
(declare-const Str8 String)
(declare-const Str17 String)
(assert (distinct (str.++ "" "rvhhcn" "" Str8 (int.to.str 56)) (str.++ "" (int.to.str i7) "" Str17) Str17))
(check-sat)
