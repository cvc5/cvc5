; COMMAND-LINE: --bv-to-bool
(set-logic ALL)
(set-info :status sat)
(declare-fun c () (Array (_ BitVec 2) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 1)))
(declare-fun a () (_ BitVec 2))
(declare-fun ag () (_ BitVec 1))
(declare-fun ak () (_ BitVec 2))
(assert (and (= a ((_ zero_extend 1) (select b (_ bv0 2)))) (= (_ bv1 1)
  (bvsdiv (bvcomp a ak) (bvand (ite (= (_ bv0 1) (bvcomp ag (select c (bvadd a
  (_ bv1 2))))) (_ bv1 1) (_ bv0 1)) (ite (= b (store (store c (bvadd a (_ bv1
  2)) ag) ak (_ bv1 1))) (_ bv1 1) (_ bv0 1)))))))
(check-sat)
