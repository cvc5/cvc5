; EXPECT: unsat
(set-logic ALL)
(declare-fun y () Int)
(assert (or false (and (distinct 0 0) (bvule ((_ int2bv 1) y) (_ bv0 1)))))
(check-sat)
