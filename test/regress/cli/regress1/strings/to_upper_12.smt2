; COMMAND-LINE: --strings-exp --seq-array=lazy --strings-code-elim
; EXPECT: sat
(set-logic QF_SLIA)
(declare-const X String)
(assert (= (str.to_upper X) (str.to_lower X)))
(assert (>= (str.len X) 12))
(check-sat)
