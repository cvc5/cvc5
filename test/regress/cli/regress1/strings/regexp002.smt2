(set-info :smt-lib-version 2.6)
(set-logic QF_S)
(set-info :status sat)
(set-option :strings-exp true)

(declare-fun x () String)
(declare-fun y () String)

(assert (str.in_re x
		(re.* (re.++ (re.* (str.to_re "a") ) (str.to_re "b") ))
	))

(assert (str.in_re y
		(re.* (re.++ (re.* (str.to_re "a") ) (str.to_re "b") ))
	))

(assert (not (= x y)))
(assert (= (str.len x) (str.len y)))
(assert (= (str.len y) 3))

(check-sat)
