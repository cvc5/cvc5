(set-logic ALL)
(set-info :status sat)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 4)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 4)))
(declare-fun o () (_ BitVec 1))
(declare-fun h () (_ BitVec 32))
(declare-fun i () (_ BitVec 32))
(declare-fun j () (_ BitVec 32))
(declare-fun l () (_ BitVec 32))
(declare-fun m () (_ BitVec 32))
(assert (= (_ bv1 1) (bvmul (ite (= (_ bv1 1) (ite (= h (_ bv0 32)) (_ bv1 1)
  (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvnor (bvcomp o (ite (= l (bvor ((_
  zero_extend 28) (select b (bvadd i (_ bv3 32)))) (bvlshr ((_ zero_extend 28)
  (select b (bvudiv i (_ bv1 32)))) ((_ zero_extend 28) (select b (bvadd i (_
  bv2 32))))))) (_ bv1 1) (_ bv0 1))) (bvsmod (ite (= (_ bv0 1) (ite (= i (_
  bv1 32)) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvshl (ite (= (_ bv1 1)
  (ite (= b (store (store (store (store a (bvadd j (_ bv3 32)) (_ bv0 4))
  (bvsdiv j (_ bv2 32)) (_ bv1 4)) (bvadd j (_ bv1 32)) (_ bv0 4)) j ((_
  extract 3 0) l))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (ite (= (_ bv0
  32) (bvor ((_ zero_extend 28) (select a (bvadd m (_ bv3 32)))) (bvadd (bvor
  ((_ zero_extend 28) (select a (bvadd m (_ bv1 32)))) ((_ zero_extend 28)
  (select a (bvnor m (_ bv0 32))))) ((_ zero_extend 28) (select a (bvadd m (_
  bv2 32))))))) (_ bv1 1) (_ bv0 1))))))))
(check-sat)
