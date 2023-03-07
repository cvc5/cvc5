(set-logic HO_ALL)

(set-info :status sat)

(declare-fun A () (Set Int))
(declare-fun B () (Set Int))
(declare-fun f (Int) Int)

(declare-const x Int)
(declare-const y1 Int)
(declare-const y2 Int)
(declare-const y3 Int)

(assert (distinct x y1 y2 y3))
(assert (set.member x  A))
(assert (set.member y1 B))
(assert (set.member y2 B))
(assert (set.member y3 B))
(assert (= B (set.map f A)))

(check-sat)
