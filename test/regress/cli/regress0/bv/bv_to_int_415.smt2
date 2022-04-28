; EXPECT: 
; SCRUBBER: grep -v "higher.order"
; EXIT: 1
(set-option :solve-bv-as-int sum)
(set-logic HO_ALL)
(declare-sort _u0 0)
(declare-const _x108 (Bag (_ BitVec 4)) )
(declare-fun _x113 ((_ BitVec 4)) _u0)
(assert (= (bag.map _x113 _x108) (as bag.empty (Bag _u0))))
(check-sat)
