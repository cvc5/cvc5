; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)                                                          
(assert (str.prefixof (str.from_int (* 20 (str.len a))) (str.substr (str.from_code 0) 0 2))) 
(check-sat)    
