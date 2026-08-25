; COMMAND-LINE: --check-models
; EXPECT: sat
(set-logic QF_AFP)
(declare-fun a () (Array Float32 Float32))
(declare-fun b () (Array Float32 Float32))
(declare-fun c () Float32)
(assert (distinct a b))
(assert (= (select a (_ +oo 8 24)) (select a (_ -oo 8 24))))
(assert (distinct c (select a (_ +oo 8 24))))
(check-sat)
