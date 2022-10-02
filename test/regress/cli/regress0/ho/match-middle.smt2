; EXPECT: unsat
(set-logic HO_UFLIA)
(set-info :status unsat)
(declare-fun f (Int Int Int) Int)
(declare-fun h (Int Int Int) Int)
(declare-fun g (Int Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)

(assert (or (= (f a) g) (= (h a) g)))

(assert (= (f a b d) c))
(assert (= (h a b d) c))

(assert (forall ((x Int) (y Int)) (not (= (g x y) c))))

(check-sat)
