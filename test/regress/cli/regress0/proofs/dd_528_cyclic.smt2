; EXPECT: unsat
(set-logic ALL)
(set-option :check-proofs true)
(assert (> real.pi (seq.nth (seq.rev (seq.++ (seq.unit real.pi) (seq.unit real.pi))) (seq.len (seq.unit real.pi)))))
(check-sat)
