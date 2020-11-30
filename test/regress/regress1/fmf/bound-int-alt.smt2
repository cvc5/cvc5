; COMMAND-LINE: --finite-model-find --fmf-bound-int
; EXPECT: sat
(set-logic UFLIA)
(set-info :status sat)
(declare-sort U 0)
(declare-sort V 0)
(declare-fun P (U Int V Int U Int) Bool)

(assert (forall ((x U) (y Int) (z V) (w Int) (v U) (d Int)) (=> (and (<= 0 d 1) (<= 2 y 6) (<= 40 w (+ 37 y))) (P x y z w v d))))

(declare-fun a () U)
(declare-fun b () V)

(assert (not (P a 2 b 40 a 0)))
(assert (not (P a 6 b 39 a 0)))
(assert (not (P a 6 b 44 a 0)))

(check-sat)
