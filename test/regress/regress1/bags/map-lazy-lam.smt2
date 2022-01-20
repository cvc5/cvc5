; COMMAND-LINE: --fmf-bound --uf-lazy-ll
; EXPECT: sat
(set-logic HO_ALL)
(define-fun f ((x String)) Int 1)
(define-fun cardinality ((A (Bag String))) Int
  (bag.count 1 (bag.map f A)))
(declare-fun A () (Bag String))
(assert (= (cardinality A) 20))
(check-sat)
