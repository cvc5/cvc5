; COMMAND-LINE: --strings-eager-len-re
; EXPECT: unsat
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.in_re x (re.+ (str.to_re "YY"))))
(assert (> 2 (str.len x)))
(check-sat)
