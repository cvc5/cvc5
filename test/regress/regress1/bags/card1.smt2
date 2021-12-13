; COMMAND-LINE: --fmf-bound --uf-lazy-ll
; EXPECT: sat
(set-logic HO_ALL)
(define-fun f ((x String)) Int 1)
(declare-fun A () (Bag String))
(assert (= (bag.card A) 20))
(check-sat)
