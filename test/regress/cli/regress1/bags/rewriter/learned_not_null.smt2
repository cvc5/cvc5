; COMMAND-LINE: --learned-rewrite
; REQUIRES: unrestricted-mode
; --learned-rewrite is not supported with proofs or unsat cores because
; the preprocessing pass does not track its non-local reasoning.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; NOT_NULL_COLUMNS by a learned fact: column 1 of Y is never null, so its null
; test in the filter is true
(set-logic HO_ALL)
(set-info :status unsat)
(declare-const Y (Bag (Tuple Int (Nullable Int))))
(assert (= (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
                         (= ((_ tuple.select 1) t) (as nullable.null (Nullable Int))))
                       Y)
           (as bag.empty (Bag (Tuple Int (Nullable Int))))))
(assert (not (= (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
                              (and (nullable.is_some ((_ tuple.select 1) t))
                                   (> ((_ tuple.select 0) t) 3)))
                            Y)
                (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
                              (> ((_ tuple.select 0) t) 3))
                            Y))))
(check-sat)
