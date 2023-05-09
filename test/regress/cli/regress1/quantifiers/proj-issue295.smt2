; COMMAND-LINE: -q --sygus-inst
; EXPECT: sat
(set-logic ALL)
(set-option :strings-exp true)
(set-info :status sat)
(assert (forall ((x Int)) (not (= (str.++ "V" "s") (str.++ "V" (str.substr (str.substr "VZ" 0 x) 0 1))))))
(check-sat)
