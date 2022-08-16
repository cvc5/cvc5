; COMMAND-LINE: --produce-interpolants -q --strings-exp --check-models
; EXPECT: fail
(set-logic ALL)
(declare-fun a () String)                                                       
(declare-fun b () Int)                                                          
(assert (not (= 0 (ite (str.contains (str.at a 0) "O") 1 0))))                  
(get-interpolant c (not (= 1 b)) ((d Bool) (e Int))                             
                 ((d Bool ((< e e))) (e Int (2 (mod e e))))) 
