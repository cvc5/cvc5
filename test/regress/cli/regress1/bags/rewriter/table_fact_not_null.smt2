; REQUIRES: unrestricted-mode
; NOT_NULL_COLUMNS by a fact: column 1 of Y is never null, so the lemma of the
; fact makes its null test in the map true, and the two maps equal
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const Y (Bag (Tuple Int (Nullable Int))))
(assert (= (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
                         (= ((_ tuple.select 1) t) (as nullable.null (Nullable Int))))
                       Y)
           (as bag.empty (Bag (Tuple Int (Nullable Int))))))
(assert (not (= (bag.map (lambda ((t (Tuple Int (Nullable Int))))
                           (tuple (ite (nullable.is_some ((_ tuple.select 1) t))
                                       (nullable.val ((_ tuple.select 1) t))
                                       0)))
                         Y)
                (bag.map (lambda ((t (Tuple Int (Nullable Int))))
                           (tuple (nullable.val ((_ tuple.select 1) t))))
                         Y))))
(check-sat)
