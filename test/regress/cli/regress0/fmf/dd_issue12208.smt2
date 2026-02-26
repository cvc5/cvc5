; COMMAND-LINE: --finite-model-find --fmf-mbqi=none
; EXPECT: sat
(set-logic UFCDT)
(declare-datatypes ((N 0)) (((Nat_zero_) (Nat_succ_ (s N)))))
(declare-datatypes ((B 0)) (((B))))
(declare-fun N (N N) Bool)
(declare-sort G 0)
(declare-fun r (G) N)
(assert (forall ((y G)) (or (and (not (N (r y) (r y))) (exists ((x G)) (= (r x) (s (r x))))) (not (is-Nat_succ_ (r y))))))
(declare-fun Na (N N) B)
(declare-sort G_ 0)
(declare-fun p (G_) N)
(assert (forall ((a G_)) (= (Na (p a) (p a)) (ite (is-Nat_zero_ (p a)) B (Na (p a) (s (p a)))))))
(check-sat)
