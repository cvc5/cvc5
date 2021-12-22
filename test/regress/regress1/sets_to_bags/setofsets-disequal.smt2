; On a production build (as of 2014-05-16), takes several minutes
; to finish (2967466 decisions).

(set-logic QF_BVFS)
(set-info :status unsat)

(define-sort myset () (Bag (Bag (_ BitVec 1))))
(declare-fun S () myset)

; 0 elements
(assert (not (= S (as bag.empty myset))))

; 1 element is S
(assert (not (= S (set.singleton (as bag.empty (Bag (_ BitVec 1)))))))
(assert (not (= S (set.singleton (set.singleton (_ bv0 1)) ))))
(assert (not (= S (set.singleton (set.singleton (_ bv1 1)) ))))
(assert (not (= S (set.singleton (bag.union_disjoint (set.singleton (_ bv0 1))
                                  (set.singleton (_ bv1 1)))))))

; 2 elements in S
(assert (not (= S (bag.union_disjoint (set.singleton (as bag.empty (Bag (_ BitVec 1))))
                         (set.singleton (set.singleton (_ bv0 1)))) )))
(assert (not (= S (bag.union_disjoint (set.singleton (as bag.empty (Bag (_ BitVec 1))))
                         (set.singleton (set.singleton (_ bv1 1)))))))
(assert (not (= S (bag.union_disjoint (set.singleton (as bag.empty (Bag (_ BitVec 1))))
                         (set.singleton (bag.union_disjoint (set.singleton (_ bv0 1))
                                         (set.singleton (_ bv1 1))))))))
(assert (not (= S (bag.union_disjoint (set.singleton (bag.union_disjoint (set.singleton (_ bv0 1))
                                         (set.singleton (_ bv1 1))))
                         (set.singleton (set.singleton (_ bv0 1)))) )))
(assert (not (= S (bag.union_disjoint (set.singleton (set.singleton (_ bv0 1)))
                         (set.singleton (set.singleton (_ bv1 1))))   )))
(assert (not (= S (bag.union_disjoint (set.singleton (bag.union_disjoint (set.singleton (_ bv0 1))
                                         (set.singleton (_ bv1 1))))
                         (set.singleton (set.singleton (_ bv1 1)))))))

; 3 elements in S
(assert (not (= S (bag.union_disjoint (set.singleton (set.singleton (_ bv1 1)))
                         (bag.union_disjoint (set.singleton (as bag.empty (Bag (_ BitVec 1))))
                                (set.singleton (set.singleton (_ bv0 1)))))  )))
(assert (not (= S (bag.union_disjoint (set.singleton (bag.union_disjoint (set.singleton (_ bv0 1))
                                         (set.singleton (_ bv1 1))))
                         (bag.union_disjoint (set.singleton (as bag.empty (Bag (_ BitVec 1))))
                                (set.singleton (set.singleton (_ bv1 1)))))  )))
(assert (not (= S (bag.union_disjoint (set.singleton (bag.union_disjoint (set.singleton (_ bv0 1))
                                         (set.singleton (_ bv1 1))))
                         (bag.union_disjoint (set.singleton (set.singleton (_ bv0 1)))
                                (set.singleton (set.singleton (_ bv1 1)))))  )))
(assert (not (= S (bag.union_disjoint (set.singleton (bag.union_disjoint (set.singleton (_ bv0 1))
                                         (set.singleton (_ bv1 1))))
                         (bag.union_disjoint (set.singleton (as bag.empty (Bag (_ BitVec 1))))
                                (set.singleton (set.singleton (_ bv0 1)))))  )))

; 4 elements in S
(assert (not (= S (bag.union_disjoint (set.singleton (bag.union_disjoint (set.singleton (_ bv0 1))
                                         (set.singleton (_ bv1 1))))
                         (bag.union_disjoint (set.singleton (set.singleton (_ bv1 1)))
                                (bag.union_disjoint (set.singleton (as bag.empty (Bag (_ BitVec 1))))
                                       (set.singleton (set.singleton (_ bv0 1))))))  )))

(check-sat)

; if you delete any of the above assertions, you should get sat
; (get-model)
