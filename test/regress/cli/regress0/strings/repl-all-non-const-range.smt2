; EXPECT: sat
(set-logic QF_SLIA)
(declare-fun r () String)
(assert (= (str.replace_all "baab" "a" r) "brrb"))
(check-sat)
