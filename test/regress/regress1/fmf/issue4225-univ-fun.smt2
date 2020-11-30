; COMMAND-LINE: --finite-model-find --uf-ho
; EXPECT: unknown
(set-logic ALL)
; this is not handled by fmf
(assert (forall ((a (-> Int Int)) (b Int)) (not (= (a b) 0))))
(check-sat)
