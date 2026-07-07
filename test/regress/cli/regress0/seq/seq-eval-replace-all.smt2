; EXPECT: unsat
(set-logic ALL)
(assert (=
(seq.replace_all
(seq.++ (seq.unit 1) (seq.unit 2))
(seq.unit 1)
(as seq.empty (Seq Int)))
(seq.unit 1)))
(check-sat)
