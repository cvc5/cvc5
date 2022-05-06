; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: unsat
(set-logic QF_ANIA)                       
(declare-fun _substvar_16_ () Int)        
(push 1)                                  
(assert (not (= (mod _substvar_16_ 2) 0)))
(check-sat)                               
(pop 1)                                   
(assert (= (- (mod _substvar_16_ 2) 2) 0))
(check-sat)     
