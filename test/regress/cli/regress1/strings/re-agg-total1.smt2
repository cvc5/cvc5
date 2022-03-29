(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-info :status unsat)
(set-option :strings-exp true)
(set-option :re-elim agg)
(declare-const x String)
(declare-const y String)


(assert (str.in_re x (re.* (str.to_re "ab") ) ) )
(assert (str.in_re x (re.* (str.to_re "abab") ) ) )
(assert (str.in_re x (re.* (str.to_re "ababac") ) ) )

(assert (> (str.len x)  1) )

(check-sat)
