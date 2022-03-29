(set-logic ALL)

(set-option :produce-models true)
(set-option :incremental true)

(declare-const A (Bag String))
(declare-const B (Bag String))
(declare-const C (Bag String))
(declare-const x String)

; union disjoint does not distribute over intersection
; sat
(check-sat-assuming
 ((distinct
   (bag.inter_min (bag.union_disjoint A B) C)
   (bag.union_disjoint (bag.inter_min A C) (bag.inter_min B C)))))


(get-value (A))
(get-value (B))
(get-value (C))
(get-value ((bag.inter_min (bag.union_disjoint A B) C)))
(get-value ((bag.union_disjoint (bag.inter_min A C) (bag.inter_min B C))))

; union max distributes over intersection
; unsat
(check-sat-assuming
 ((distinct
   (bag.inter_min (bag.union_max A B) C)
   (bag.union_max (bag.inter_min A C) (bag.inter_min B C)))))

; Verify emptbag is a subbag of any bag
; unsat
(check-sat-assuming
 ((not (bag.subbag (as bag.empty (Bag String)) A))))

; find an element with multiplicity 4 in the disjoint union of
; {|"a", "a", "b", "b", "b"|} and {|"b", "c", "c"|}
(check-sat-assuming
 ((= 4
     (bag.count x
                (bag.union_disjoint
                 (bag.union_disjoint (bag "a" 2) (bag "b" 3))
                 (bag.union_disjoint (bag "b" 1) (bag "c" 2)))))))

; x is "b"
(get-value (x))
