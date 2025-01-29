; EXPECT: unsat
(set-logic ALL)
(declare-const a String)
(declare-const b Int)
(assert (not (str.contains (str.replace_all a "a" a) (str.at a b))))
(check-sat)
