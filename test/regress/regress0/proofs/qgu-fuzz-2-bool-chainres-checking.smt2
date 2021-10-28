; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert
(and (ite a c (ite b d c)) (= d (ite a b c)) (not (= a (ite b c d))) (ite a c (ite b d a)) (ite c (ite b a d) c) (ite a c (ite c d a)))
)
(check-sat)