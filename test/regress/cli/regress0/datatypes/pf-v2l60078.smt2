; EXPECT: unsat
(set-logic QF_DT)
(declare-datatypes ((n 0) (l 0) (t 0)) (((z)) ((ln) (nc (r l))) ((f))))
(declare-fun x () l)
(assert (and (not (= ln (r x))) (not ((_ is nc) (r x)))))
(check-sat)
