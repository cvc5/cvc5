; EXPECT: unknown
(set-logic ALL)
(set-option :produce-models true)
(set-option :fmf-bound true)

(declare-fun s () (Set Real))

(assert (> (set.card s) 2))
(assert (forall ((x Real)) (=> (set.member x s) (< x 0))))

(check-sat)
