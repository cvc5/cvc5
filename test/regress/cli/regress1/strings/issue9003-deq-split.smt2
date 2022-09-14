; EXPECT: sat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun i () Int)
(assert (xor (str.<= (str.at y i) (str.update y 0 x)) (= y (str.++ x x))))
(assert (str.in_re (str.++ x "z" y) (re.++ (re.* (re.++ (str.to_re "b") (str.to_re "z"))) (str.to_re "b"))))
(assert (str.in_re x (re.* (re.range "a" "u"))))
(check-sat)
