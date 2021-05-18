; COMMAND-LINE:
; EXPECT: sat
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun e () Int)
(declare-fun f () Bool)
(assert (= (div a e) (- 1)))
(assert (= f (not (= e (- 1)))))
(assert (ite f false (= (div a (- 1)) (- 1))))
(set-info :status sat)
(check-sat)
