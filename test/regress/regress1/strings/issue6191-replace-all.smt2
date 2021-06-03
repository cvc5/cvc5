; COMMAND-LINE: --strings-exp --no-strings-lazy-pp
; EXPECT: sat
(set-logic ALL)
(declare-fun x_9 () String)                                                        
(declare-fun literal_19 () String)                                                 
(declare-fun x_20 () String)                                                       
(assert (= literal_19 "\u{3c}\u{64}\u{69}\u{76}"))                                 
(assert (= x_9 (str.replace_all x_9 x_20 x_9)))                                    
(assert (= "\u{3c}\u{2" x_20))                                                     
(assert (str.<= "\u{3c}\u{" literal_19))                                           
(check-sat)
