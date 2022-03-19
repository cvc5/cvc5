; COMMAND-LINE: --sort-inference --finite-model-find
; EXPECT: unsat
; DISABLE-TESTER: unsat-core
(set-logic ALL)
(assert (not (exists ((X Int)) (not (= X 12)) )))
(check-sat)

