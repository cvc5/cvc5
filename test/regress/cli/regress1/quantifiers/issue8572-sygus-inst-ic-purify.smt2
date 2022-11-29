; COMMAND-LINE: --strings-exp --sygus-inst
; EXPECT: unsat
(set-logic ALL)
(assert (forall ((e String)) (= 0 (ite (str.contains (str.substr e 0 (- (str.len e) 1)) "/") 1 0))))
(check-sat)
