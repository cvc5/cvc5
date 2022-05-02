(set-info :smt-lib-version 2.6)
(set-logic QF_S)
(set-option :strings-exp true)
(set-option :strings-fmf true)
(set-info :status sat)

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

(check-sat)
