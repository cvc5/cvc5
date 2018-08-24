; COMMAND-LINE: --no-check-models --sep-pre-skolem-emp
; EXPECT: sat
(set-logic QF_ALL_SUPPORTED)
(assert (not (_ emp Int Int)))
(check-sat)
