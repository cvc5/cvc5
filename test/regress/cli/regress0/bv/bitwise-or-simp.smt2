; EXPECT: unsat
(set-logic ALL)
(declare-fun x () (_ BitVec 4))
(assert (not (=
(bvor #b0100 x #b0001) (bvor #b0101 x))))
(check-sat)
