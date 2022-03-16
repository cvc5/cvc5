; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(set-info :status sat)

(declare-fun x () String)
(declare-fun i () Int)

(assert (= (str.at x i) "b"))
(assert (and (>= i 4) (< i (str.len x))))
(assert (< (str.len x) 7))
(assert (> (str.len x) 2))

(check-sat)
