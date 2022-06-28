; COMMAND-LINE: --strings-exp --seq-array=lazy
; EXPECT: sat
(set-logic QF_SLIA)
(declare-const X String)
(assert (= (str.to_upper X) (str.to_lower X)))
(assert (>= (str.len X) 12))
(check-sat)
