; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(assert (= x #b0101))
(assert (= y #b0101))
(check-sat-assuming ( (not (let ((_let_1 (bvneg x))) (let ((_let_2 ((_ zero_extend 4) x))) (let ((_let_3 ((_ zero_extend 4) y))) (and (and (and (= (bvmul _let_2 _let_3) (bvmul _let_3 _let_2)) (not (bvult x y))) (bvule (bvsub _let_2 _let_3) (bvadd _let_2 ((_ zero_extend 4) _let_1)))) (= x (bvsub _let_1 (bvadd x #b0001)))))))) ))
