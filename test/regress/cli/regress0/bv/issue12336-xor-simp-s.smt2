; EXPECT: unsat
(set-logic QF_BV)
(declare-const r (_ BitVec 4))
(assert (= #b0001 (bvxor r (bvnot r))))
(check-sat)
