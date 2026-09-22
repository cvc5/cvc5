; EXPECT: unsat
(set-logic ALL)
(declare-const x String)

(assert (not (str.contains x "A")))
(assert (not (str.contains x "B")))
(assert (not (str.contains x "C")))

(assert (= (str.to_code (str.substr x 2 1)) 66))
(check-sat)
