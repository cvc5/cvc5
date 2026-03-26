; EXPECT: unsat
(set-logic ALL)
(declare-fun s () String)
(assert (= s "\u{30000}"))
(assert (= (str.len s) 1))
(check-sat)
