; COMMAND-LINE: -q
; EXPECT: unsat
(set-logic ALL)
(set-option :miniscope-quant true)
(set-option :sygus-inference true)
(set-option :var-ineq-elim-quant false)
(set-info :status unsat)
(declare-fun b ( Int ) Bool)
(assert (forall (( c Int ) ( d Int )) (and (> d 3 ) (xor (>= c d) (b c)))))  
(check-sat)   
