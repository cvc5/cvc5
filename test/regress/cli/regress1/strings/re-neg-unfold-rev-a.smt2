(set-info :smt-lib-version 2.6)
(set-logic QF_S)
(set-info :status unsat)


(declare-const x String)
(declare-const y String)
(assert (and (= y "foobar") (str.in_re x (re.++ (str.to_re "ab") (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "b")))))
(assert (not (and (= y "foobar") (str.in_re x (re.++ (str.to_re "a") (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "b") (re.* re.allchar) (str.to_re "b"))))))
(check-sat)
