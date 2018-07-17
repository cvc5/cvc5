; COMMAND-LINE: --no-check-models --sep-pre-skolem-emp
; EXPECT: sat
(set-logic QF_ALL_SUPPORTED)
(assert (not (emp 0 0)))
(check-sat)
