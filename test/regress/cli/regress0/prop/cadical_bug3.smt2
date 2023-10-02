; COMMAND-LINE: -i --sat-solver=cadical
; EXPECT: unknown
; EXPECT: unknown
(set-logic UF)
(declare-sort U 0)
(declare-fun a (U U) U)
(declare-fun m (U U) Bool)
(declare-fun s () U)
(assert (and (forall ((l U)) (not (m s l))) (forall ((l U)) (or (and (m s s)) (m l (a s s))))))
(push 1)
(set-info :status unknown)
(check-sat)
(pop 1)
(set-info :status unknown)
(check-sat)
