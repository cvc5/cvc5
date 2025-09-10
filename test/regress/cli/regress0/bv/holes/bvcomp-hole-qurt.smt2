; EXPECT: unsat
(set-logic ALL)
(declare-fun fp.f1 () (_ BitVec 64))
(assert (not
(= (bvcomp ((_ extract 63 63) fp.f1) #b0) (bvnot ((_ extract 63 63) fp.f1)))
))
(check-sat)
