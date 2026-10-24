; REQUIRES: normaliz
; DISABLE-TESTER: proof
; COMMAND-LINE: --bags-to-liastar
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun A () (Bag Int))
(declare-fun B () (Bag Int))
; the negation of the valid identity
;   |A inter B| + |A union B| = |A| + |B|
; which follows from min(p, q) + max(p, q) = p + q at every element
(assert (not (= (+ (bag.card (bag.inter_min A B)) (bag.card (bag.union_max A B)))
                (+ (bag.card A) (bag.card B)))))
(check-sat)
