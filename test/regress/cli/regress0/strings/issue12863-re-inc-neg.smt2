; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(set-info :status unsat)
; The second membership below is included in the first. It must not be marked
; inactive before the first is unfolded, which happens at last call effort.
(declare-fun y () String)
(declare-fun v () String)
(assert (not (str.in_re v (re.* (re.union (str.to_re "7") (re.* (re.union (str.to_re "0") (str.to_re y))))))))
(assert (not (str.in_re v (re.* (re.union (str.to_re "0") (str.to_re y))))))
(assert (= v "0"))
(check-sat)
