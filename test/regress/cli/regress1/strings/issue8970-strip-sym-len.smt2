; EXPECT: sat
(set-logic QF_SLIA)
(declare-fun t () String)
(assert (str.prefixof "-" (str.substr t 0 1)))
(assert (> (str.len (str.substr t 0 2)) 1))
(assert (= "-0" (str.update "-0" 0 t)))
(assert (str.suffixof (str.replace t "-0" "-") "-"))
(check-sat)
