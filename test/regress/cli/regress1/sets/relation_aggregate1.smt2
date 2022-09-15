(set-logic HO_ALL)

(set-info :status sat)

(set-option :fmf-bound true)
(set-option :uf-lazy-ll true)

(define-fun sumByCategory ((x (Tuple String String Int)) (y (Tuple String Int))) (Tuple String Int)
  (tuple
   ((_ tuple.select 0) x)
   (+ ((_ tuple.select 2) x) ((_ tuple.select 1) y))))

(declare-fun categorySales () (Set (Tuple String Int)))

;(define-fun categorySales () (Set (Tuple String Int))
;  (set.union
;   (set.singleton (tuple "Software" 5))
;   (set.singleton (tuple "Hardware" 4))))

(assert
 (= categorySales
    ((_ rel.aggr 0)
      sumByCategory
      (tuple "" 0)
      (set.union
       (set.singleton (tuple "Software" "win" 1))
       (set.singleton (tuple "Software" "mac" 4))
       (set.singleton (tuple "Hardware" "cpu" 2))
       (set.singleton (tuple "Hardware" "gpu" 2))))))

(check-sat)
