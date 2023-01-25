; COMMAND-LINE: --produce-interpolants
; EXPECT: sat
(set-logic ALL)
(declare-fun v () (Set Int))
(declare-fun a () (Set Int))
(assert (and (forall ((Set Int)) (= 1 (set.card (set.inter (set.inter v v) (set.minus v a)))))))
(check-sat)
