(set-logic QF_S)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun x () String)

(assert (str.in.re x
		(re.* (re.++ (re.* (str.to.re "a") ) (str.to.re "b") ))
	))

(assert (= (str.len x) 3))

(check-sat)
