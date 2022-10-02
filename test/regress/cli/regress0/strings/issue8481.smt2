; COMMAND-LINE: --strings-eager-len-re
; EXPECT: sat
(set-logic QF_S)
(declare-fun a () String)
(declare-fun b () String)
(assert (str.in_re (str.replace b a "") (re.++ (str.to_re "u") (re.union (str.to_re "b") (str.to_re "")))))
(assert (= (str.to_int (str.++ a a)) 0))
(check-sat)
