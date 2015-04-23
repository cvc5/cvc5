(set-logic QF_S)
(set-info :status sat)
(set-option :strings-exp true)

(declare-const s String)

(assert (str.in.re s (re.inter
	(re.++ (str.to.re "a") (re.* (str.to.re "b")) 
		(re.inter (str.to.re "c") (re.* (str.to.re "c"))))
	(re.++ (str.to.re "a") (re.* (str.to.re "b")) (re.* (str.to.re "c")))
	)))

(check-sat)
