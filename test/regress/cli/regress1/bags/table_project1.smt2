(set-logic HO_ALL)
(set-info :status sat)

(declare-fun A () (Table String Int String Bool))
(declare-fun B () (Table Int Bool String String))
(declare-fun C () (Table String String))
(declare-fun D () Table)

(assert
 (= A
    (bag.union_disjoint
     (bag (tuple "x" 0 "y" false) 5)
     (bag (tuple "x" 1 "z" true) 10))))

; (bag.union_disjoint (bag (tuple 0 false "x" "y") 5) (bag (tuple 1 true "x" "z") 10)))
(assert (= B ((_ table.project 1 3 0 2) A)))
; (bag (tuple "x" "x") 15)
(assert (= C ((_ table.project 0 0) A)))
; (bag tuple 15)
(assert (= D (table.project A)))
(check-sat)
