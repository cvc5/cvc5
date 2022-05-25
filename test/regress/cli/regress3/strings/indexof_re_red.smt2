; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(declare-const x String)
(declare-const i Int)

(assert (= i (str.indexof_re x (re.++ re.all (str.to_re "a")) 0)))
(assert (not (or (= i 0) (= i (- 1)))))
(set-info :status unsat)
(check-sat)
