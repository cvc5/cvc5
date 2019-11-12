(set-logic ALL_SUPPORTED)
(set-option :strings-exp true)
(set-info :status sat)
(declare-fun a () String) 
(declare-fun b () String) 
(declare-fun c () String) 
(assert 
    (and              
        (and                                      
            (and                          
                (not (= (ite (= (str.at (str.substr c 1 (- (str.len (str.substr c 0 (- (str.len c) 1))) 1)) (- (str.len (str.substr (str.substr c 1 (- (str.len (str.replace a b "")) 1)) 0 (- (str.len (str.substr (str.replace a b "") 1 (- (str.len (str.replace a b "")) 1))) 1))) 1)) "\t") 1 0) 0))   
                   
                (= (ite (= (str.at (str.substr (str.substr c 1 (- (str.len (str.replace a b "")) 1)) 0 (- (str.len (str.substr (str.replace a b "") 1 (- (str.len (str.replace a b "")) 1))) 1)) 0) "\n") 1 0) 0)
            )     
                            
            (= (ite (= (str.at (str.substr (str.substr c 1 (- (str.len c) 1)) 0 (- (str.len (str.substr (str.replace a b "") 1 (- (str.len (str.replace a b "")) 1))) 1)) 0) " ") 1 0) 0)                   
            (not (= (ite (= (str.at (str.substr (str.replace a b "") 1 (- (str.len c) 1)) (- (str.len (str.substr c 1 (- (str.len c) 1))) 1)) "\v") 1 0) 0))
        )       
        (= (ite (= (str.at (str.substr c 1 (- (str.len (str.replace a b "")) 1)) 0) " ") 1 0) 0)
    )
)
; may trigger F_EndpointEmp inference
(check-sat) 
