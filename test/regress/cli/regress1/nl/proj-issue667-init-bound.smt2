; EXPECT: unknown
(set-logic ALL)
(set-option :produce-unsat-cores true)
(set-option :proof-prune-input true)
(assert (>= real.pi (/ real.pi (cot (- (arccos (sin real.pi)))))))
(check-sat)
