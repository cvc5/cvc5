(set-logic QF_LIRAFS)
(set-info :status sat)

(declare-fun s () (Set (Set Real)))
(declare-fun t () (Set (Set Real)))

(declare-fun x () (Set Real))
(declare-fun y () (Set Real))

(assert (member 0.5 y))
(assert (member y s))
(assert (or (= s t) (= s (singleton (singleton 1.0))) (= s (singleton (singleton 0.0)))))

(check-sat)
