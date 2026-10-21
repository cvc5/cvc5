; REQUIRES: unrestricted-mode
; COMMAND-LINE: --parsing-mode=lenient
; EXPECT: unsat
(set-logic QF_DT)
(declare-datatype T ((C) (D)))
(assert (is-C D))
(check-sat)
