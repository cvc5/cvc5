; COMMAND-LINE: --finite-model-find
; EXPECT: unknown
(set-logic HO_ALL)
; this is not handled by fmf
(assert (forall ((a (-> Int Int)) (b Int)) (not (= (a b) 0))))
(check-sat)
