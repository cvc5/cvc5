; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
; the negation of |A + B| = |A| + |B|
(assert (not (= (bag.card (bag.union_disjoint A B))
                (+ (bag.card A) (bag.card B)))))
(check-sat)
