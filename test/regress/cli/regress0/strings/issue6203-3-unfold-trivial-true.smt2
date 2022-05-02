; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-fun s () String)
(assert (str.in_re s (re.* (re.union (str.to_re "A") (str.to_re s)))))
(assert (not (str.in_re s (re.* (re.opt (re.comp (str.to_re "A")))))))
(check-sat)
