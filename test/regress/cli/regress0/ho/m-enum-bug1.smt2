; COMMAND-LINE: --mbqi --mbqi-fast-sygus
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort a 0)
(declare-fun y () a)
(assert 
    (not 
        (exists ((F (-> a a)) (X a)) 
            (= 
                (F X) 
                y
            )
        )
    )
)
(set-info :filename SEU882^5)
(check-sat-assuming ( true ))
