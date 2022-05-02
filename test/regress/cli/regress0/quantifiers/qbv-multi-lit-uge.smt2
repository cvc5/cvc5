; COMMAND-LINE: --cegqi-bv
; EXPECT: sat
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 3))
(declare-fun b () (_ BitVec 3))
(declare-fun c () (_ BitVec 3))

(assert (forall ((x (_ BitVec 3))) (or (not (= (bvmul x a) b)) (bvuge x c))))

(check-sat)
