; COMMAND-LINE: --model-based-arith-bv-conv
; EXPECT: sat
(set-logic ALL)
(declare-fun x () (_ BitVec 8))
(declare-fun c () Int)
(assert (bvule #b00100000 x))
(assert (bvule x #b00100011))
(assert (< 30 c 35))
(assert (or (= (bv2nat x) c) (= (bv2nat x) (+ c 2))))
(check-sat)
