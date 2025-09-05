; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(declare-datatypes ((p 0)) (((P))))
(declare-datatypes ((l 0)) (((N) (C (c p) (s l)))))
(declare-datatypes ((n 0)) (((z) (S (s n)))))
(declare-sort r 0)
(declare-fun B (n p) l)
(declare-fun p (r) n)
(declare-fun r (r) p)
(assert (forall ((x r)) (and (or (exists ((a r)) (= (p a) (s (p x))))) (= (B (p x) (r x)) (ite ((_ is S) (p x)) (C (r x) (B (s (p x)) (r x))) N)))))
(declare-fun m (n n) n)
(assert (and (exists ((a r)) (= (p a) (m z z)))))
(check-sat)
