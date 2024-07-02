; COMMAND-LINE: --finite-model-find
; EXPECT: unknown
(set-logic ALL)
(declare-fun b (Int) Int)
(declare-fun u (Int) Int)
(assert (forall ((v Int)) (not (= v (b (+ 1 (* (- 1) (div 0 (u v)))))))))
(assert true)
(check-sat)
