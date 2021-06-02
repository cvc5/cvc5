; EXPECT: unsat
(set-logic QF_ALL)
(set-info :status unsat)
(declare-datatypes ((Pair 2)) ((par (T S) ((pair (first T) (second S))))))

(declare-datatypes ((Color 0)) (((red) (blue))))

(declare-fun p1 () (Pair Color Color))
(declare-fun p2 () (Pair Color Color))
(declare-fun p3 () (Pair Color Color))
(declare-fun p4 () (Pair Color Color))
(declare-fun p5 () (Pair Color Color))

(assert (distinct p1 p2 p3 p4 p5))
(check-sat)
