; EXPECT: unsat
(set-logic ALL)
(declare-sort g 0)
(declare-sort c 0)
(declare-datatypes ((u 0)) (((uc))))
(declare-fun i (u (Array Int Bool) (Array Int g) (Array Int c)) Bool)
(assert (forall ((a u)) (forall ((s (Array Int Bool))) (forall ((t (Array Int g))) (forall ((st (Array Int c))) (! (distinct true (i a s t st)) :pattern ((i uc s t st))))))))
(assert (exists ((u u) (o (Array Int c)) (t (Array Int Bool)) (e (Array Int g))) (= true (i uc t e o))))
(check-sat)
