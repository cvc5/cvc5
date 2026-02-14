; COMMAND-LINE: --tc-mode=model-based
; EXPECT: sat
(set-logic ALL)
(declare-datatypes ((x5 0)) (((x3c) (x4c))))
(declare-sort x 0)
(declare-datatypes ((x22 0)) (((x22c))))
(declare-datatypes ((x2 0)) (((x2c (x2s x5) (x24 x5) (x25 Int) (x26 Int) (x27 Int)))))
(declare-datatypes ((x54 0)) (((x49 (x48 x22)) (x54c (x5s x2)))))
(declare-fun x5f (x22) x2)
(declare-fun x67 () (Array x x54))
(declare-fun x6 () (Array x x54))
(declare-fun xf () x)
(assert (distinct x3c (ite (or (= x67 (store x67 xf (x54c (x2c x4c x3c (x25 (x5f (x48 (select x67 xf)))) (x26 (x5f (x48 (select x67 xf)))) (x27 (x5f (x48 (select x6 xf))))))))) x3c x4c)))
(check-sat)
