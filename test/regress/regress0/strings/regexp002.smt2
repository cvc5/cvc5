(set-logic QF_S)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun x () String)
(declare-fun y () String)

(assert (str.in.re x
		(re.* (re.++ (re.* (str.to.re "a") ) (str.to.re "b") ))
	))

(assert (str.in.re y
		(re.* (re.++ (re.* (str.to.re "a") ) (str.to.re "b") ))
	))

(assert (not (= x y)))
(assert (= (str.len x) (str.len y)))
(assert (= (str.len y) 3))

(check-sat)
