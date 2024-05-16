; COMMAND-LINE: --mbqi --mbqi-fast-sygus
; EXPECT: unsat
(set-logic HO_ALL)
(declare-sort a 0)
(declare-fun f () a)
(declare-fun g () a)
(assert 
    (not 
        (=> 
            (forall ((P (-> a Bool))) 
                (=> 
                    (P f) 
                    (P g)
                )
            ) 
            (forall ((R (-> a Bool))) 
                (=> 
                    (R g) 
                    (R f)
                )
            )
        )
    )
)
(set-info :filename LCL579^2)
(check-sat-assuming ( true ))
