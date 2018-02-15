; COMMAND-LINE: --cbqi-bv --cbqi-bv-ineq=keep
; EXPECT: sat
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))

(assert (not (= a #x00)))

(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8))) (or 
(not (= (bvmul x y) #x0A))
(not (= (bvadd y a) #x10))
)))

(check-sat)
