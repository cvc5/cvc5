; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(declare-fun a () String)
(assert (not (= a (str.replace_re_all a (re.++ (re.* re.allchar) (str.to_re a) (re.* re.allchar)) a))))
(set-info :status unsat)
(check-sat)
