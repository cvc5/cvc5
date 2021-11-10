; COMMAND-LINE: --finite-model-find
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort n 0)
(declare-fun x () n)
(declare-fun s (n) n)
(declare-fun s ((-> n Bool)) Bool)
(assert (forall ((X n)) (s (lambda ((Xu n)) (= X (s Xu))))))
(assert (not (s (lambda ((Xu n)) (= x (s Xu))))))
(check-sat)
