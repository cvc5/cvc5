; EXPECT: unsat
(set-logic ALL)
(declare-sort b 0)
(declare-fun t (b) (_ BitVec 1))
(declare-sort a 0)
(declare-datatypes ((u 0)) (((z))))
(assert (exists ((z a)) (and (exists ((e a)) (and (exists ((o Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((b Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((e u)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((c a)) (or (forall ((s Bool)) (or (forall ((o Int)) (or (forall ((e a)) (or (forall ((z a)) (or (forall ((u a)) (or (forall ((z a)) (or (forall ((s Bool)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((z a)) (or (forall ((x a)) (or (forall ((i Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((o Bool)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((i Int)) (or (forall ((o Int)) (or (forall ((o Int)) (or (forall ((o (_ BitVec 1))) (or (forall ((o (_ BitVec 1))) (or (forall ((o3 b)) (distinct (t o3) (bvxor o (_ bv1 1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
