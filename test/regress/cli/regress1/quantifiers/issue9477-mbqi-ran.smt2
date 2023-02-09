; COMMAND-LINE: --mbqi
; EXPECT: unknown
(set-logic UFNRA)
(declare-fun c (Real) Bool)
(assert (forall ((z Real)) (or (not (= (c z) (c 0.0))) (not (= (* z z) 2.0)))))
(check-sat)
