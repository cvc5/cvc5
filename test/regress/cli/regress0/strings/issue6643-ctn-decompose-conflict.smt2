; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(declare-fun y () String)
(declare-fun z () String)
(assert (not (= (str.contains y (str.replace "A" "" z)) (str.contains y "A"))))
(set-info :status sat)
(check-sat)
