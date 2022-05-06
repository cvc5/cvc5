; COMMAND-LINE: --cegqi-bv --no-cegqi-full
; EXPECT: sat
(set-logic BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))

(assert (forall ((x (_ BitVec 8))) (or (bvuge x (bvadd a b)) (bvule x b))))

(check-sat)
