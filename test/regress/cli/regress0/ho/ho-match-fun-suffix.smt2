; EXPECT: unsat
(set-logic HO_ALL)
(set-info :status unsat)
(declare-fun f (Int Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)

(assert (forall ((x (-> Int Int)) (y Int)) (not (= (x y) 0))))

(assert (= (f a b) 0))

(check-sat)