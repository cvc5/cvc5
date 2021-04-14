; COMMAND-LINE: --bv-to-bool
; EXPECT: sat
(set-logic ALL)
(declare-fun b () (Array (_ BitVec 10) (_ BitVec 1)))
(declare-fun c () (Array (_ BitVec 10) (_ BitVec 1)))
(declare-fun ae () (_ BitVec 10))
(declare-fun ag () (_ BitVec 10))
(declare-fun ak () (_ BitVec 10))
(assert (= (_ bv1 1) (bvand (bvcomp ae ((_ zero_extend 9) (select b (_ bv0
  10)))) (bvsdiv (bvcomp ae ak) (bvand (ite (= (_ bv0 1) (bvcomp ag (bvshl ((_
  zero_extend 9) (select c (bvadd ae (_ bv3 10)))) (_ bv8 10)))) (_ bv1 1) (_
  bv0 1)) (ite (= b (store (store c (bvadd ae (_ bv3 10)) ((_ extract 0 0)
  (bvlshr ag (_ bv8 10)))) ak (_ bv1 1))) (_ bv1 1) (_ bv0 1)))))))
(check-sat)