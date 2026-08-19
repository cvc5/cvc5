; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun y () String)
(declare-fun v () String)
(assert (not (str.in_re v (re.++ (re.+ (re.union (str.to_re "7") (re.* (re.union (str.to_re "0") (str.to_re y))))) (re.* (str.to_re "c"))))))
(assert (or (= v "0") (= v "")))
(check-sat)
