; COMMAND-LINE:
; EXPECT: sat
(set-logic LRA)
(set-info :status sat)
(declare-fun c () Real)
(assert (forall ((x Real)) (or (<= x 0) (>= x (+ c 3)))))
(check-sat)
