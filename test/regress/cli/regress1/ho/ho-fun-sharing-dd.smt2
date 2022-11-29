; COMMAND-LINE: --finite-model-find
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort n 0)
(declare-fun x () n)
(declare-fun s (n) n)
(declare-fun t ((-> n Bool)) Bool)
(assert (forall ((X n)) (t (lambda ((Xu n)) (= X (s Xu))))))
(assert (not (t (lambda ((Xu n)) (= x (s Xu))))))
(check-sat)
