; EXPECT: unsat
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ "abcd" x "efghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz") (str.++ "abcd" y "aabcdefghijklmnopqrstuvwxyz")))
(check-sat)
