; EXPECT: sat
(set-logic ALL)
(set-info :status sat)

(declare-fun r1 () (Relation String Int))
(declare-fun r2 () (Relation Int String))
(declare-fun r () (Relation String String))
(declare-fun s () (Relation String String))
(declare-fun t () (Relation String Int Int String))
(declare-fun lt1 () (Relation Int Int))
(declare-fun lt2 () (Relation Int Int))
(declare-fun i () Int)

(assert (= r1 (set.insert (tuple "a" 1) (tuple "b" 2) (tuple "c" 3) (set.singleton (tuple "d" 4)))))
(assert (= r2 (set.insert (tuple 1 "1") (tuple 2 "2") (tuple 3 "3") (set.singleton (tuple 17 "17")))))
(assert (= r (rel.join r1 r2)))
(assert (= s (rel.transpose r)))
(assert (= t (rel.product r1 r2)))
(assert (= lt1 (set.insert (tuple 1 2) (tuple 2 3) (tuple 3 4) (set.singleton (tuple 4 5)))))
(assert (= lt2 (rel.tclosure lt1)))
(assert (= i (set.card t)))

(check-sat)
