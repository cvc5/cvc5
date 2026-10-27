; EXPECT: unsat
(set-logic ALL)
(declare-fun s () String)
(declare-fun t () String)
(assert (= (str.replace_re_all "CAAA" (re.* (str.to_re "A")) t) t))
(assert (str.contains t "A"))
(check-sat)
