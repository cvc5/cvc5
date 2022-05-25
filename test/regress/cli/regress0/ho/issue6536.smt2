; COMMAND-LINE: --strings-exp --mbqi
; EXPECT: sat
(set-logic HO_ALL)
(declare-datatypes ((a 0) (b 0)) (((c) (d)) ((h (j b)) (e))))
(declare-fun f () b)
(declare-fun k (a) b)
(declare-fun g (b b) b)
(assert (forall ((i a)) (distinct (k i) (ite ((_ is c) i) e (ite ((_ is d) i) (h (g (k  i) (k  i))) f)))))
(check-sat)
