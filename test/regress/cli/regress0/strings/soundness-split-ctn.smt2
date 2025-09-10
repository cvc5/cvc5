; EXPECT: sat
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(assert (str.contains (str.++ x "A" y) "CAC"))
(assert (not (str.contains x "CAC")))
(assert (not (str.contains y "CAC")))
(check-sat)
