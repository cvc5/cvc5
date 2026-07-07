(set-logic HO_ALL)
(set-info :status sat)
(define-fun map_fun ((i Int)) Int (+ i 1))
(define-fun filter_fun ((i Int)) Bool (and (>= i 0) (<= i 10)))

(declare-fun IntBag        () (Bag Int))
(declare-fun FiltMapIntBag () (Bag Int))

(declare-fun min_bag () Int)

(assert (distinct IntBag (as bag.empty (Bag Int))))

(assert (= FiltMapIntBag (bag.map map_fun (bag.filter filter_fun IntBag))))

(assert 
(= IntBag 
  (bag.union_disjoint 
    (bag.union_disjoint (bag 1 1) (bag 2 1))
    (bag.union_disjoint (bag 4 1) (bag 5 1)))))

; get the minumum of FiltMapIntBag
(assert (bag.member min_bag FiltMapIntBag))
(assert (bag.all (lambda ((i Int)) (>= i min_bag)) FiltMapIntBag))      
(check-sat)
