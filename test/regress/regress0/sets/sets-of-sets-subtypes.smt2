(set-logic QF_LIRAFS)
(set-info :status sat)

(declare-fun s () (Set (Set Real)))
(declare-fun t () (Set (Set Real)))

(declare-fun x () (Set Real))
(declare-fun y () (Set Real))

(assert (set.member 0.5 y))
(assert (set.member y s))
(assert (or (= s t) (= s (set.singleton (set.singleton 1.0))) (= s (set.singleton (set.singleton 0.0)))))

(check-sat)
