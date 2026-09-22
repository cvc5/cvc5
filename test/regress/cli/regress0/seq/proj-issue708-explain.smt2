; EXPECT: sat
(set-logic ALL)
(set-option :check-proofs true)
(set-option :strings-eager-eval false)
(declare-const x (Seq Bool))
(assert (seq.contains (seq.++ (seq.unit x) (seq.unit (seq.rev x))) (seq.++ (seq.unit (seq.unit (seq.contains x (seq.rev x)))) (seq.unit x))))
(check-sat)
