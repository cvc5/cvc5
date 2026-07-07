; EXPECT: unsat
(set-logic ALL)
(declare-const x Int)
(declare-sort m 0)
(declare-datatypes ((u 0)) (((uc))))
(assert (exists ((b u)) (not (=> (bvule ((_ int_to_bv 8) (mod x 256)) (_ bv0 8)) false (forall ((o m)) false)))))
(check-sat)
