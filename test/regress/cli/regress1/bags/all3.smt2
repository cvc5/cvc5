(set-logic HO_ALL)
(set-info :status unsat)

(define-fun map_fun ((i Int)) Int (+ i 1))
(define-fun filter_fun ((i Int)) Bool (and (>= i 0) (<= i 10)))

(declare-fun IntBag        () (Bag Int))
(declare-fun FiltMapIntBag () (Bag Int))

(declare-fun min_set () Int)

(assert (distinct IntBag (as bag.empty (Bag Int))))

(assert (= FiltMapIntBag (bag.map map_fun (bag.filter filter_fun IntBag))))

(assert (bag.member min_set FiltMapIntBag))
(assert (bag.all (lambda ((i Int)) (> i min_set)) FiltMapIntBag))
(check-sat)
