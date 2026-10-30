; REQUIRES: no-safe-mode
; COMMAND-LINE: --pre-skolem-quant=on
; EXPECT: unsat
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U U) Bool)
(declare-fun f (U) U)
(declare-const c U)
(assert (forall ((x U)) (! (exists ((y U)) (P x y)) :pattern ((f x)) :qid q1)))
(assert (forall ((x U) (y U)) (! (not (P x y)) :pattern ((P x y)))))
(assert (= (f c) c))
(check-sat)
