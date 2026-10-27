; EXPECT: unsat
(set-logic ALL)
(declare-const b (_ BitVec 1))
(assert (not
(= (bvcomp #b1 b) b)
))
(check-sat)
