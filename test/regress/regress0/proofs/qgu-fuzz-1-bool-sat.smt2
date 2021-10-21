; EXPECT: unsat
(set-logic QF_UF)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert (and (or d b) (= c d) (not (ite d c false)) (= (or b d) (= b d))))
(check-sat)