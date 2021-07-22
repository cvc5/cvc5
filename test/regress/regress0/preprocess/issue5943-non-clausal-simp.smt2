; COMMAND-LINE: --strings-exp
; EXPECT: unsat
(set-logic QF_SLIA)
(declare-fun s () String)
(assert (and (and (= (str.len (str.at s 3)) 4) (not (not (= (ite (not (= (ite (not (= (str.at (str.at s 3) 
(ite (not (not (= (ite (<= (str.len (str.at s 1)) 3) 1 0) 0))) 1 0)) (str.at s 5))) 1 0) 0)) 1 0) 0)))) (not (not (= (str.len s) 3)))))
(check-sat)
