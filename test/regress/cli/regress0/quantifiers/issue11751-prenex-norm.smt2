; COMMAND-LINE: --prenex-quant=norm
; EXPECT: unsat
(set-logic ALL)
(assert (forall ((v Real)) (and (= 1.0 (/ v 0.0)) (= 0.0 (/ 0.0 0.0)))))
(check-sat)
