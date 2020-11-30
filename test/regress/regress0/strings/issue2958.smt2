; COMMAND-LINE: --strings-exp
(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-const x String)
(assert (not (str.prefixof "ab" x)))
(assert (str.in_re (str.substr x 0 2) (re.++ (str.to_re "ab") (re.* (str.to_re "dcab")))))
(check-sat)
