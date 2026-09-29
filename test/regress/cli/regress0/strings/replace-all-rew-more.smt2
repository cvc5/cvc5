; EXPECT: unsat
(set-logic ALL)
(declare-fun s () String)
(declare-fun t () String)
(assert (or
(not (= (str.replace_all s t t) s))
(not (= (str.replace_all (str.++ "A" s) (str.++ "A" s) t) t))
))
(check-sat)
