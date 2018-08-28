; COMMAND-LINE: --sort-inference --finite-model-find --no-check-unsat-cores --no-check-proofs
; EXPECT: unsat
(set-logic ALL)
(assert (not (exists ((X Int)) (not (= X 12)) )))
(check-sat)

