; COMMAND-LINE: --cegqi-nested-qe
; EXPECT: sat
(set-logic LIA)
(set-option :cegqi-nested-qe true)
(set-info :status sat)
(assert (forall ((a Int)) (exists ((b Int)) (= (ite (= a 0) 0 1) (ite (= b 0) 0 1)))))
(check-sat)
