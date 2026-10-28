; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun y () String)
(assert (not (str.in_re "" (re.++ (re.* (str.to_re y)) (re.* re.allchar)))))
(check-sat)
