; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(declare-fun a () String)
; A complicated way of saying a = "b"
(assert (str.in_re a (re.++ (re.* (re.opt (str.to_re a))) (str.to_re "b"))))
; Corresponds to replace_re_all("ab", a*b, "") contains "a"
(assert (str.contains (str.replace_re_all (str.++ "a" a) (re.++ (re.* (str.to_re "a")) (str.to_re "b")) "") "a"))
(set-info :status unsat)
(check-sat)
