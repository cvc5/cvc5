; EXPECT: unknown
(set-logic ALL)
(set-option :sets-exp true)
(set-option :dump-proofs true)
(declare-const x Bool)
(assert (and (>= (set.choose (ite x (set.singleton real.pi) (as set.universe (Set Real)))) (arccos real.pi)) (ite (set.member (arccos real.pi) (set.singleton real.pi)) (set.member (arccos real.pi) (set.complement (set.singleton real.pi))) true)))
(check-sat)
