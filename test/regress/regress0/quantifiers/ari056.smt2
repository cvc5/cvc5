; COMMAND-LINE: --cegqi
; EXPECT: unsat
(set-logic UFNIRA)
(set-info :status unsat)
(assert (forall ((X Int)) (= X 12) ))
(check-sat)
