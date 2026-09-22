; EXPECT: unsat
(set-logic ALL)
(declare-fun x () (_ BitVec 4))
(assert (not (=
(bvand #b1011 x #b1110) (bvand #b1010 x))))
(check-sat)
