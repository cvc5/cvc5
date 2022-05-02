; EXPECT: unsat
(set-logic ALL)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert (and (or d (ite c false true)) (not (= d (or b c))) (= d (ite c d (not d)))))
(check-sat)
