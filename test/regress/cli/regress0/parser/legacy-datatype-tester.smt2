; COMMAND-LINE:
; COMMAND-LINE: --no-strict-parsing
; EXPECT: unsat
(set-logic QF_DT)
(declare-datatype T ((C) (D)))
(assert (is-C D))
(check-sat)
