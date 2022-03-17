(set-info :smt-lib-version 2.6)
(set-logic QF_S)
(set-info :status sat)
(set-option :strings-exp true)

(declare-const s String)

(assert (str.in_re s (re.inter
	(re.++ (str.to_re "a") (re.* (str.to_re "b")) 
		(re.inter (str.to_re "c") (re.* (str.to_re "c"))))
	(re.++ (str.to_re "a") (re.* (str.to_re "b")) (re.* (str.to_re "c")))
	)))

(check-sat)
