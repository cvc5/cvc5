(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-info :status unsat)
(set-option :strings-exp true)
(set-option :re-elim-agg true)
(declare-const x String)
(declare-const y String)


(assert (str.in.re x (re.* (str.to.re "ab") ) ) )
(assert (str.in.re x (re.* (str.to.re "abab") ) ) )
(assert (str.in.re x (re.* (str.to.re "ababac") ) ) )

(assert (> (str.len x)  1) )

(check-sat)
