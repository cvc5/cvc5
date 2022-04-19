(set-logic HO_ALL)

(set-info :status sat)

(set-option :fmf-bound true)
(set-option :uf-lazy-ll true)

; equivalence relation : inverse
(define-fun r ((x Int) (y Int)) Bool (= 0 (+ x y)))

(declare-fun A () (Bag Int))
(declare-fun B () (Bag (Bag Int)))

(assert
 (= A
    (bag.union_disjoint
     (bag 1 20) (bag (- 1) 50)
     (bag 2 30) (bag (- 2) 60)
     (bag 3 40) (bag (- 3) 70)
     (bag 4 100))))

;(define-fun B () (Bag (Bag Int))
;  (bag.union_disjoint (bag (bag 4 100) 1)
;                      (bag (bag.union_disjoint (bag 1 20) (bag (- 1) 50)) 1)
;                      (bag (bag.union_disjoint (bag 2 30) (bag (- 2) 60)) 1)
;                      (bag (bag.union_disjoint (bag 3 40) (bag (- 3) 70)) 1)))
(assert (= B (bag.partition r A)))

(check-sat)

