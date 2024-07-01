; COMMAND-LINE: --finite-model-find -q
(set-logic HO_ALL)
(set-info :status sat)
(define-fun map_fun ((i Int)) Int (+ i 1))
(define-fun filter_fun ((i Int)) Bool (and (>= i 0) (<= i 10)))

(declare-fun IntSet        () (Set Int))
(declare-fun FiltMapIntSet () (Set Int))

(declare-fun min_set () Int)

(assert (not (set.is_empty IntSet)))

(assert (= FiltMapIntSet (set.map map_fun (set.filter filter_fun IntSet))))

; get the minumum of FiltMapIntSet
(assert (set.member min_set FiltMapIntSet))
(assert (set.all (lambda ((i Int)) (>= i min_set)) FiltMapIntSet))

(check-sat)
