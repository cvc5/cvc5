; COMMAND-LINE: --uf-ho
; EXPECT: sat
(set-logic UF)
(set-info :status sat)
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-fun g (U) U)
(declare-fun h (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(assert (distinct (f a) g h))
(check-sat)
