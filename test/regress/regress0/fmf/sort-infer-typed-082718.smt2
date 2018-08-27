; COMMAND-LINE: --sort-inference --finite-model-find --no-check-unsat-cores
; EXPECT: unsat
(set-option :incremental false)
(set-logic ALL)
(assert (not (exists ((X Int)) (not (= X 12)) )))
(check-sat)

