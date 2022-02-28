(set-logic ALL)
(set-info :status sat)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))
(declare-fun d () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun e () (_ BitVec 32))
(declare-fun ep () (_ BitVec 32))
(declare-fun eq () (_ BitVec 32))
(assert (= (_ bv1 1) (bvand (bvashr (bvsdiv (_ bv1 1) (ite (= (_ bv1
1) (ite (= b (_ bv1 32)) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)))
(ite (= (_ bv0 1) (ite (= eq (bvadd c a)) (_ bv1 1) (_ bv0 1))) (_ bv1
1) (_ bv0 1))) (ite (= (ite (= ep (bvadd eq (_ bv4 32))) (_ bv1 1) (_
bv0 1)) (ite (= e (bvshl (concat (_ bv0 24) (select d (bvadd ep (_ bv3
32)))) (_ bv24 32))) (_ bv1 1) (_ bv0 1)) (ite (= (_ bv1 1) (ite (= (_
bv1 32) (bvlshr e (_ bv31 32))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0
1))) (_ bv1 1) (_ bv0 1)))))
(check-sat)
