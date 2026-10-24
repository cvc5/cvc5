; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Int))
; folding (+ 1 .) over A counts its elements, so the fold is the cardinality
; of A, which is 2 and not 5. The bound of the quantifier of the reduction of
; bag.fold is the cardinality of A, so the star propagates it instead of the
; solver guessing it.
(assert (= (bag.card A) 2))
(assert (= (bag.fold (lambda ((x Int) (y Int)) (+ 1 y)) 0 A) 5))
(check-sat)
