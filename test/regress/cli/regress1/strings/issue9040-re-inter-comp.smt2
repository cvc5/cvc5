; COMMAND-LINE: --re-inter=all --strings-exp
; EXPECT: sat
(set-logic ALL)
(declare-fun e () String)
(assert (distinct (str.in_re e (re.* (str.to_re "b"))) (ite (str.in_re e (re.* (re.comp (str.to_re "")))) (= e "") false)))
(check-sat)
