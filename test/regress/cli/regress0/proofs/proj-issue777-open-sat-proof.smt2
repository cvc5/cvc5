; EXPECT: unsat
(set-logic QF_UF)
(declare-const a Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert (or (and (ite c a false) (ite (or a d) (not b) a) (ite d (= b (ite b true d)) b)) false))
(check-sat)