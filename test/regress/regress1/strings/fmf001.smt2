(set-logic QF_S)
(set-option :strings-exp true)
(set-option :strings-fmf true)
(set-info :status sat)

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

(check-sat)
