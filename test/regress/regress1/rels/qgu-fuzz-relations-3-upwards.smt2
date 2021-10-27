(set-logic ALL)
(set-info :status sat)
(declare-fun a () (Set (Tuple Int Int)))
(declare-fun b () (Set (Tuple Int Int)))
(declare-fun c () Int)
(declare-fun d () (Tuple Int Int))
(assert (let ((_let_1 (join b b))) (let ((_let_2 (join a a))) (let ((_let_3 (tclosure b))) (let ((_let_4 (join b a))) (and (= _let_2 _let_4) (= a (transpose (tclosure _let_1))) (= _let_3 _let_1) (= a (join b (join a _let_2))) (= (join a b) _let_4) (not (= b _let_3)) (= _let_2 _let_1)))))))

(check-sat)
