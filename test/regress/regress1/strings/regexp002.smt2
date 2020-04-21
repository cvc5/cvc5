(set-info :smt-lib-version 2.6)
(set-logic QF_S)
(set-info :status sat)
(set-option :strings-exp true)
; this option requires user to check whether the constraint is in the fragment
; currently we do not provide only positive membership constraint checking
; if users use this option but the constraint is not in this fragment, the result will fail
(set-option :strings-inm true)

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
