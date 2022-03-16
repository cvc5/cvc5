; COMMAND-LINE: --nl-ext=none
; EXPECT: sat
; REQUIRES: poly
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun _substvar_15_ () Real)                                                                                                                                 
(declare-fun _substvar_17_ () Real)                                                                                                                                 
(assert (let ((?v_1 (<= 0.0 _substvar_15_))) (and ?v_1 (and ?v_1 (and ?v_1 (= (* _substvar_15_ _substvar_15_) (+ 1 (* _substvar_17_ (* _substvar_17_ (- 1)))))))))) 
(check-sat)     
