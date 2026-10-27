; EXPECT: unsat
(set-logic ALL)
(declare-fun s () String)
(assert (= (str.rev (str.to_lower s)) (str.to_upper s)))
(assert (not (= s (str.to_lower s))))
(assert (not (= s (str.to_upper s))))
(assert (< (str.len s) 2))
(check-sat)
