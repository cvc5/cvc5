; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(declare-fun a () String)
(assert (= (str.len a) 2))
(assert (= (str.len (str.replace_re_all a (str.to_re "A") "B")) 3))
(set-info :status unsat)
(check-sat)
