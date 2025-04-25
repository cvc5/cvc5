; COMMAND-LINE: --mbqi --mbqi-enum
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort a 0)
(declare-fun p (a) Bool)
(declare-fun y () a)
(assert  
    (forall ((M (-> (-> a a) Bool))) 
        (exists ((G (-> a a))) 
            (and 
                (M G) 
                (and 
                    (p y)
                    (not (p (G y)))
                )
            )
        )
    )
)
(set-info :filename SEU926^5)
(check-sat-assuming ( true ))
