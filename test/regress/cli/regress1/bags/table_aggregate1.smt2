(set-logic HO_ALL)

(set-info :status sat)

(set-option :fmf-bound true)
(set-option :uf-lazy-ll true)

(define-fun sumByCategory ((x (Tuple String String Int)) (y (Tuple String Int))) (Tuple String Int)
  (tuple
   ((_ tuple.select 0) x)
   (+ ((_ tuple.select 2) x) ((_ tuple.select 1) y))))

(declare-fun categorySales () (Bag (Tuple String Int)))

;(define-fun categorySales () (Bag (Tuple String Int))
;  (bag.union_disjoint
;   (bag (tuple "Hardware" 10) 1)
;   (bag (tuple "Software" 6) 1)))

(assert
 (= categorySales
    ((_ table.aggr 0)
      sumByCategory
      (tuple "" 0)
      (bag.union_disjoint
       (bag (tuple "Software" "win" 1) 2)
       (bag (tuple "Software" "mac" 4) 1)
       (bag (tuple "Hardware" "cpu" 2) 2)
       (bag (tuple "Hardware" "gpu" 3) 2)))))

(check-sat)
