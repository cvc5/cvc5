(set-info :smt-lib-version 2.6)
(set-logic QF_S)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun x () String)

(assert (not (= x "")))
(assert (not (str.in_re x (re.++ (str.to_re "AB") (re.* (str.to_re "A"))))))
(assert (not (str.in_re x (re.++ (re.* (str.to_re "A")) (str.to_re "B")))))

(check-sat)
