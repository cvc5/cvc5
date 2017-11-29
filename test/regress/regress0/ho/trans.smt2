; COMMAND-LINE: --uf-ho
; EXPECT: unsat
(set-logic UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun h (U) U)
(declare-fun a () U)
(assert (= f g))
(assert (= g h))
(assert (not (= f h)))
(check-sat)
