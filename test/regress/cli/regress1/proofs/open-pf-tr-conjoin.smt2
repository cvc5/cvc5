; EXPECT: unsat
(set-logic ALL)
(declare-const x Bool)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (and x (= c (ite (= c 0) 1 0)) (= x (and (distinct b 1) (distinct a 1)))))
(assert (= 1 (ite (= c 0) 1 0)))
(check-sat)
