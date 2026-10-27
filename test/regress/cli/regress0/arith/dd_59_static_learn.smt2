; EXPECT: unsat
(set-logic ALL)
(declare-fun n () String)
(assert (>= (+ (- (- 1) 1) (ite (< (str.len n) 1) (str.len n) 1)) 0))
(check-sat)
