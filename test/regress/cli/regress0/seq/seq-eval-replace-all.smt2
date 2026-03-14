; EXPECT: unsat
(set-logic ALL)
(assert (=
(seq.replace_all (seq.++
(seq.unit 0)
(seq.unit 1)
(seq.unit 2)
(seq.unit 1)
(seq.unit 2)
(seq.unit 3))
(seq.++
(seq.unit 1)
(seq.unit 2)
)
(seq.unit 1))
(seq.unit 1)))
(check-sat)
