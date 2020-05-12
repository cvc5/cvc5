; COMMAND-LINE: --strings-exp --no-re-elim
; EXPECT: unsat
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun x () String)
(assert (not (=                                                                                                                                                     
(let ((_let_0 (re.* re.allchar ))) 
(str.in_re x (re.++ re.allchar  _let_0 (str.to_re "AC") _let_0 (str.to_re "CA") _let_0)))                                        
(let ((_let_0 (+ 0 1))) (let ((_let_1 (str.indexof x "AC" _let_0))) (and (not (= _let_1 (- 1))) (not (= (str.indexof x "CA" (+ _let_1 (str.len "AC"))) (- 1))))))   
)))        
(assert (<= (str.len x) 8))
; adding --strings-fmf to command line above incorrectly said "sat" for this at ad0b69e6
(check-sat)
