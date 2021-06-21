(set-logic ALL)
(set-info :status sat)
(assert (str.in_re "A" (ite (= (div 0 0) 0) (str.to_re "A") (str.to_re "B"))))
(check-sat)
