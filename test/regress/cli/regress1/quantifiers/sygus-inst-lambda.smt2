; COMMAND-LINE: --sygus-inst
; EXPECT: unsat
(set-logic HO_ALL)
(define-sort a () Int)
(declare-fun z ((-> a a)) a)
(declare-fun g (a) Bool)
(assert 
    (forall ((H (-> a a))) 
        (g (z H))
    )
)
(assert 
    (forall ((H (-> a a))) 
        (not (g (H (z H))))
    )
)
(check-sat)
