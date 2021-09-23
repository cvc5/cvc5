; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic QF_S)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x "B" y) (re.* (re.++ (str.to_re "A") (re.union (re.* (str.to_re "A")) (str.to_re "B"))))))
(assert (str.in_re y (str.to_re "A")))
(check-sat)
