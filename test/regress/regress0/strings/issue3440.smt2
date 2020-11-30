; COMMAND-LINE: --no-strings-lazy-pp
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic QF_S)
(set-info :status sat)
(declare-fun a () String)                                                       
(declare-fun b () String)                                                       
(declare-fun c () String)                                                       
(declare-fun d () String)                                                       
(assert (= (str.replace a b "") (str.++ c d)))                                  
(check-sat)   
