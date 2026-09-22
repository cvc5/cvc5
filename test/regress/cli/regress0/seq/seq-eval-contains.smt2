; EXPECT: unsat
(set-logic ALL)
(assert
(not
(seq.contains
(seq.++ (seq.unit 1) (seq.unit 2))
(seq.unit 1))))
(check-sat)
