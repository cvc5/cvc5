(set-logic HO_ALL)

(set-info :status sat)

(declare-fun A () (Relation String Int String Bool))
(declare-fun B () (Relation Int Bool String String))
(declare-fun C () (Relation String String))
(declare-fun D () Relation)

(assert
 (= A
    (set.union
     (set.singleton (tuple "x" 0 "y" false))
     (set.singleton (tuple "x" 1 "z" true)))))


; (set.union (set.singleton (tuple 0 false "x" "y")) (set.singleton (tuple 1 true "x" "z")))
(assert (= B ((_ rel.project 1 3 0 2) A)))

; (set.singleton (tuple "x" "x"))
(assert (= C ((_ rel.project 0 0) A)))

; (set.singleton tuple)
(assert (= D (rel.project A)))

(check-sat)
