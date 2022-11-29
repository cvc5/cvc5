; EXPECT: 
; SCRUBBER: grep -v "higher.order"
; EXIT: 1
(set-option :solve-bv-as-int sum)
(set-logic HO_ALL)
(declare-const _x108 (Bag (_ BitVec 4)) )
(declare-fun _x113 ((_ BitVec 4)) (_ BitVec 4))
(assert (= (bag.map _x113 _x108) (as bag.empty (Bag (_ BitVec 4)))))
(check-sat)
