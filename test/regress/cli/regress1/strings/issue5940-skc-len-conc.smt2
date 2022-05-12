; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(define-fun z () Int 0)                                                            
(define-fun y () String "")                                                        
(define-fun x () String "")                                                        
(assert (= "B" (str.replace (str.substr "A" 0 z) "" 
             (str.replace "B" (str.substr "B" 0 0) (str.substr "A" 0 z)))))
(check-sat)
