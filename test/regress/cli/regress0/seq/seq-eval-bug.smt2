; EXPECT: unsat
(set-logic ALL)
(declare-fun d () Int)
(declare-fun e () Int)
(assert (str.contains (seq.unit d) (seq.++ (seq.unit d) (seq.unit e))))
(check-sat)
