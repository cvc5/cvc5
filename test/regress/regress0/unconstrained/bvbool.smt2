; COMMAND-LINE: --unconstrained-simp
(set-logic QF_AUFBVLIA)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun x0 () (_ BitVec 10))
(declare-fun x1 () (_ BitVec 10))
(declare-fun x2 () (_ BitVec 10))
(declare-fun x3 () (_ BitVec 10))
(declare-fun x4 () (_ BitVec 10))
(declare-fun p1 () Bool)
(declare-fun p2 () Bool)
(declare-fun p3 () Bool)
(declare-fun v2 () Int)
(declare-fun a2 (Int) (_ BitVec 1024))
(declare-fun v3 () (_ BitVec 1024))
(declare-fun v4 () (_ BitVec 1024))
(declare-fun v5 () (_ BitVec 1024))
(assert
 (not
  (=
   (a2
    (ite 
     (=> (or (and (= (bvnor (bvnand (bvor (bvand x0 x1) x2) x3) x4) ((_ extract 9 0) v3)) p1) p2) p3)
     v2
     6)
    )
   (bvudiv (bvudiv v4 v5) (bvudiv (bvudiv v3 v4) (bvudiv v3 v5))))
  )
 )
(check-sat)
(exit)
