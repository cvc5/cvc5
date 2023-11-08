; COMMAND-LINE: --no-cegqi --mbqi
; EXPECT: unsat
; REQUIRES: poly
(set-logic NRA)
(set-info :status unsat)
(assert (forall ((x Real)) (or (< x 0.0) (not (= (* x x) 2.0)))))
(check-sat)
