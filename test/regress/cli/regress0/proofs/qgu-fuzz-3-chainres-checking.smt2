; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert (and (= a (ite (or c d) d a)) (not (ite d a false)) (ite c a d)))
(check-sat)