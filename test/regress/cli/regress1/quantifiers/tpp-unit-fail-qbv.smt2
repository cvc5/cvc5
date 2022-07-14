; DISABLE-TESTER: lfsc
(set-logic BV)
(set-info :status unsat)
(declare-fun t () (_ BitVec 4))
(declare-fun s () (_ BitVec 4))
(assert
(distinct (bvult t (bvnot (bvneg s))) (exists ((BOUND_VARIABLE_273 (_ BitVec 4))) (bvugt (bvurem BOUND_VARIABLE_273 s) t)))
)
(check-sat)
