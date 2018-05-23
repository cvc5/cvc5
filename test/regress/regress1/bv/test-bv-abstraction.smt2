; COMMAND-LINE: --bv-abstraction
(set-logic QF_BV)
(set-info :status sat)
(declare-fun x0 () (_ BitVec 8))
(declare-fun x1 () (_ BitVec 8))
(declare-fun y0 () (_ BitVec 8))
(declare-fun y1 () (_ BitVec 8))
(declare-fun y2 () (_ BitVec 8))
(assert
 (or
  (= x0 (bvadd (bvmul (_ bv2 8) y0) y1))
  (= x0 (bvadd (bvmul (_ bv2 8) y1) y2))
  (= x0 (bvadd (bvmul (_ bv2 8) y2) y0))
 )
)
(assert
 (or
  (= x1 (bvadd (bvadd (bvmul (_ bv3 8) y0) (bvmul (_ bv2 8) x0)) (_ bv5 8)))
  (= x1 (bvadd (bvadd (bvmul (_ bv3 8) y1) (bvmul (_ bv2 8) x0)) (_ bv5 8)))
  (= x1 (bvadd (bvadd (bvmul (_ bv3 8) x0) (bvmul (_ bv2 8) y2)) (_ bv5 8)))
 )
)
(check-sat)
(exit)
