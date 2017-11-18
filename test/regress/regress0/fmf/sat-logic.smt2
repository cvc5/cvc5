; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic SAT)
(set-info :status sat)
(assert (forall ((x Bool) (y Bool)) (exists ((z Bool)) (= z (and x y)))))
(check-sat)
