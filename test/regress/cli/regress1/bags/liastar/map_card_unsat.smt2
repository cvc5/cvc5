; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Int))
(define-fun f ((i Int)) Int (+ i 1))
; the map moves every occurrence of an element of A to an occurrence of its
; image, so the two bags have the same cardinality
(assert (= (bag.card A) 3))
(assert (> (bag.card (bag.map f A)) 3))
(check-sat)
