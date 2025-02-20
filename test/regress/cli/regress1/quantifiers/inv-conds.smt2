; EXPECT: unsat
(set-logic ALL)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(declare-fun r () (_ BitVec 8))
(assert (or

(and (not (exists ((x (_ BitVec 4))) (= (bvmul x s) t))) (= (bvand (bvor (bvneg s) s) t) t))
(and (not (exists ((x (_ BitVec 4))) (= (bvudiv x s) t))) (= (bvudiv (bvmul s t) s) t))
(and (not (exists ((x (_ BitVec 4))) (= (bvudiv s x) t))) (= (bvudiv s (bvudiv s t)) t))
(and (not (exists ((x (_ BitVec 4))) (= (bvurem x s) t))) (bvuge (bvnot (bvneg s)) t))
(and (not (exists ((x (_ BitVec 4))) (= (bvurem s x) t))) (bvuge (bvand (bvsub (bvadd t t) s) s) t))
(and (not (exists ((x (_ BitVec 4))) (= (bvor s x) t))) (= t (bvor t s)))
(and (not (exists ((x (_ BitVec 4))) (= (bvand s x) t))) (= t (bvand t s)))
(and (not (exists ((x (_ BitVec 4))) (= (bvashr x s) t))) (let ((_let_1 (bvult s #b0100))) (and (=> _let_1 (= (bvashr (bvshl t s) s) t)) (=> (not _let_1) (or (= t #b1111) (= t #b0000))))))
(and (not (exists ((x (_ BitVec 4))) (= (bvashr s x) t))) (or (= s t) (= (bvashr s #b0001) t) (= (bvashr s #b0010) t) (= (bvashr s #b0011) t) (= (bvashr s #b0100) t)))
(and (not (exists ((x (_ BitVec 4))) (= (bvshl x s) t))) (= (bvshl (bvlshr t s) s) t))
(and (not (exists ((x (_ BitVec 4))) (= (bvshl s x) t))) (or (= s t) (= (bvshl s #b0001) t) (= (bvshl s #b0010) t) (= (bvshl s #b0011) t) (= (bvshl s #b0100) t)))
(and (not (exists ((x (_ BitVec 4))) (= (bvlshr x s) t))) (= (bvlshr (bvshl t s) s) t))
(and (not (exists ((x (_ BitVec 4))) (= (bvlshr s x) t))) (or (= s t) (= (bvlshr s #b0001) t) (= (bvlshr s #b0010) t) (= (bvlshr s #b0011) t) (= (bvlshr s #b0100) t)))


))
(check-sat)
