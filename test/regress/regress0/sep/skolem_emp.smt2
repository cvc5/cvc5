; COMMAND-LINE: --no-check-models --sep-pre-skolem-emp
; EXPECT: sat
(set-logic QF_ALL)
(declare-heap (Int Int))
(assert (not (_ emp Int Int)))
(check-sat)
