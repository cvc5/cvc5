(set-logic ALL)
(set-info :status unsat)
(declare-fun s () (_ BitVec 3))
(assert
 (forall ((t (_ BitVec 3)) )(not (and (distinct (bvsdiv s t) (bvneg (bvnand s t))) true)))
 )
(check-sat)
