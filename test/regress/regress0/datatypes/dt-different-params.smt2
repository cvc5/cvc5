(set-logic QF_ALL)
(set-info :status unsat)
(declare-datatypes ((Data 1)) ((par (T) ((data (first T))))))

(declare-fun q1 () (Data Int))
(declare-fun q2 () (Data Int))
(declare-fun q3 () (Data Int))

(assert (distinct q1 q2 q3))

(declare-fun p1 () (Data Bool))
(declare-fun p2 () (Data Bool))
(declare-fun p3 () (Data Bool))

(assert (distinct p1 p2 p3))
(check-sat)
