; COMMAND-LINE: --nl-ext=full --nl-ext-tplanes
; EXPECT: sat
(set-logic QF_UFNIA)
(set-info :status sat)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (not (= y 0)))
; should be SAT if the partial functions for div and mod are different
(assert (not (= (- y (* (div y x) x)) (mod y x))))
(check-sat)
