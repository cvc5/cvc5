(set-info :smt-lib-version 2.5)
(set-logic QF_S)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun x () String)

(assert (not (= x "")))
(assert (not (str.in.re x (re.++ (str.to.re "AB") (re.* (str.to.re "A"))))))
(assert (not (str.in.re x (re.++ (re.* (str.to.re "A")) (str.to.re "B")))))

(check-sat)
