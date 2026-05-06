; COMMAND-LINE: --check-models -q
; EXPECT: sat
(set-logic QF_AFP)
(declare-fun a () (Array Float32 Float32))
(declare-fun b () (Array Float32 Float32))
(assert (distinct a b))
(assert (= (select b (_ +oo 8 24)) (select b (_ -oo 8 24))))
(check-sat)
