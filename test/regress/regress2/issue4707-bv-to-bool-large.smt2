; COMMAND-LINE: --bv-to-bool
; EXPECT: sat
(set-logic ALL)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun c () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun d () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun aa () (_ BitVec 1))
(declare-fun e () (_ BitVec 1))
(declare-fun f () (_ BitVec 1))
(declare-fun ab () (_ BitVec 1))
(declare-fun g () (_ BitVec 1))
(declare-fun h () (_ BitVec 1))
(declare-fun i () (_ BitVec 1))
(declare-fun j () (_ BitVec 1))
(declare-fun k () (_ BitVec 1))
(declare-fun l () (_ BitVec 1))
(declare-fun m () (_ BitVec 1))
(declare-fun n () (_ BitVec 1))
(declare-fun o () (_ BitVec 1))
(declare-fun p () (_ BitVec 1))
(declare-fun q () (_ BitVec 1))
(declare-fun r () (_ BitVec 1))
(declare-fun s () (_ BitVec 1))
(declare-fun t () (_ BitVec 1))
(declare-fun u () (_ BitVec 1))
(declare-fun v () (_ BitVec 1))
(declare-fun w () (_ BitVec 1))
(declare-fun x () (_ BitVec 1))
(declare-fun y () (_ BitVec 1))
(declare-fun z () (_ BitVec 1))
(declare-fun ac () (_ BitVec 1))
(declare-fun ad () (_ BitVec 32))
(declare-fun ae () (_ BitVec 32))
(declare-fun af () (_ BitVec 32))
(declare-fun ag () (_ BitVec 32))
(declare-fun ah () (_ BitVec 32))
(declare-fun ai () (_ BitVec 32))
(declare-fun aj () (_ BitVec 32))
(declare-fun ak () (_ BitVec 32))
(declare-fun al () (_ BitVec 32))
(declare-fun am () (_ BitVec 32))
(declare-fun an () (_ BitVec 32))
(declare-fun ao () (_ BitVec 1))
(declare-fun ap () (_ BitVec 32))
(declare-fun aq () (_ BitVec 1))
(declare-fun ar () (_ BitVec 32))
(declare-fun au () (_ BitVec 32))
(declare-fun av () (_ BitVec 32))
(declare-fun aw () (_ BitVec 32))
(declare-fun ax () (_ BitVec 32))
(declare-fun ay () (_ BitVec 32))
(assert
 (let ((?as (bvadd av (_ bv4 32)))
    (?at (bvadd av (_ bv12 32))))
  (= (_ bv1 1) (bvand (bvand (ite (= ac (ite (= an ai) (_ bv1 1) (_
  bv0 1))) (_ bv1 1) (_ bv0 1)) (bvmul (ite (= z (ite (= ai aj) (_
  bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= y (ite (= aj
  (bvor (bvnand (bvor (concat (_ bv0 24) (select d (bvadd ak (_ bv0
  32)))) (bvshl (concat (_ bv0 24) (select d (bvadd ak (_ bv1 32))))
  (_ bv8 32))) (bvshl (concat (_ bv0 24) (select d (bvadd ak (_ bv2
  32)))) (_ bv16 32))) (bvshl (concat (_ bv0 24) (select d (bvadd ak
  (_ bv3 32)))) (_ bv24 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0
  1)) (bvand (ite (= x (ite (= ak ?as) (_ bv1 1) (_ bv0 1))) (_ bv1
  1) (_ bv0 1)) (bvand (ite (= w (ite (= d (store (store (store
  (store c (bvadd (_ bv134533664 32) (_ bv3 32)) ((_ extract 7 0)
  (bvlshr al (_ bv24 32)))) (bvadd (_ bv134533664 32) (_ bv2 32)) ((_
  extract 7 0) (bvlshr al (_ bv16 32)))) (bvadd (_ bv134533664 32) (_
  bv1 32)) ((_ extract 7 0) (bvlshr al (_ bv8 32)))) (bvadd (_
  bv134533664 32) (_ bv0 32)) ((_ extract 7 0) al))) (_ bv1 1) (_ bv0
  1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= v (ite (= al (bvor (bvor
  (bvor (concat (_ bv0 24) (select c (bvadd am (_ bv0 32)))) (bvshl
  (concat (_ bv0 24) (select c (bvadd am (_ bv1 32)))) (_ bv8 32)))
  (bvshl (concat (_ bv0 24) (select c (bvadd am (_ bv2 32)))) (_ bv16
  32))) (bvshl (concat (_ bv0 24) (select c (bvsub am (_ bv3 32))))
  (_ bv24 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand
  (ite (= u (ite (= am ?at) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0
  1)) (bvand (ite (= t ao) (_ bv1 1) (_ bv0 1)) (bvand (ite (= s (ite
  (= an ad) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (=
  r (ite (= ad ae) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand
  (ite (= q (ite (= ae (bvor (bvor (bvor (concat (_ bv0 24) (select b
  (bvadd af (_ bv0 32)))) (bvxor (concat (_ bv0 24) (select b (bvadd
  af (_ bv1 32)))) (_ bv8 32))) (bvshl (concat (_ bv0 24) (select b
  (bvadd af (_ bv2 32)))) (_ bv16 32))) (bvshl (concat (_ bv0 24)
  (select b (bvadd af (_ bv3 32)))) (_ bv24 32)))) (_ bv1 1) (_ bv0
  1))) (_ bv1 1) (_ bv0 1)) (bvsdiv (ite (= p (ite (= af ?as) (_ bv1
  1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= o (ite (= b
  (store (store (store (store c (bvadd ar (_ bv3 32)) ((_ extract 7
  0) (bvlshr ag (_ bv24 32)))) (bvadd ar (_ bv2 32)) ((_ extract 7 0)
  (bvlshr ag (_ bv16 32)))) (bvand ar (_ bv1 32)) ((_ extract 7 0)
  (bvlshr ag (_ bv8 32)))) (bvadd ar (_ bv0 32)) ((_ extract 7 0)
  ag))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= n
  (ite (= ag (bvor (bvor (bvor (concat (_ bv0 24) (select c (bvadd ah
  (_ bv0 32)))) (bvshl (concat (_ bv0 24) (select c (bvadd ah (_ bv1
  32)))) (_ bv8 32))) (bvshl (concat (_ bv0 24) (select c (bvurem ah
  (_ bv2 32)))) (_ bv16 32))) (bvshl (concat (_ bv0 24) (select c
  (bvadd ah (_ bv3 32)))) (_ bv24 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1
  1) (_ bv0 1)) (bvand (ite (= m (ite (= ah ?at) (_ bv1 1) (_ bv0
  1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= l ao ) (_ bv1 1) (_ bv0
  1)) (bvand (ite (= k (bvor (bvand t (bvand u (bvand v (bvand w
  (bvand x (bvand y (bvand z ac))))))) (bvand l (bvand m (bvand n
  (bvand o (bvand p (bvand q (bvand r s))))))))) (_ bv1 1) (_ bv0 1))
  (bvand (ite (= j (ite (= ao ((_ extract 0 0) ap)) (_ bv1 1) (_ bv0
  1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= i (ite (= ap (concat (_
  bv0 31) aq)) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite
  (= h (ite (= aq (ite (= ar (_ bv0 32)) (_ bv1 1) (_ bv0 1))) (_ bv1
  1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= g (ite (= ar
  (bvor (bvor (bvor (concat (_ bv0 24) (select c (bvadd au (_ bv0
  32)))) (bvshl (concat (_ bv0 24) (select c (bvadd au (_ bv1 32))))
  (_ bv8 32))) (bvshl (concat (_ bv0 24) (select c (bvadd au (_ bv2
  32)))) (_ bv16 32))) (bvshl (concat (_ bv0 24) (select c (bvadd au
  (_ bv3 32)))) (_ bv24 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0
  1)) (bvand (ite (= ab (ite (= au (bvadd av (_ bv8 32))) (_ bv1 1)
  (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= f (ite (= c (store
  (store (store (store a (bvadd av (_ bv3 32)) ((_ extract 7 0)
  (bvlshr ay (_ bv24 32)))) (bvadd av (_ bv2 32)) ((_ extract 7 0)
  (bvlshr ay (_ bv16 32)))) (bvadd av (_ bv1 32)) ((_ extract 7 0)
  (bvlshr ay (_ bv8 32)))) (bvadd av (_ bv0 32)) ((_ extract 7 0)
  ay))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (bvand (ite (= e
  (ite (= av (bvsub ax (_ bv4 32))) (_ bv1 1) (_ bv0 1))) (_ bv1 1)
  (_ bv0 1)) (ite (= aa (ite (= aw (bvor (bvor (bvor (concat (_ bv0
  24) (select a (bvadd ax (_ bv0 32)))) (bvshl (concat (_ bv0 24)
  (select a (bvadd ax (_ bv1 32)))) (_ bv8 32))) (bvshl (concat (_
  bv0 24) (select a (bvadd ax (_ bv2 32)))) (_ bv16 32))) (bvshl
  (concat (_ bv0 24) (select a (bvadd ax (_ bv3 32)))) (_ bv24 32))))
  (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1))))))))))))))))))))))))))
  (bvand (bvnot (_ bv0 1)) (bvand (bvand aa (bvand e (bvand f (bvand
  ab (bvand g (bvand h (bvand i (bvand j k)))))))) (ite (= aw an) (_
  bv1 1) (_ bv0 1))))))))
(check-sat)