; EXPECT: unsat
(set-logic QF_DT)
(declare-datatypes ((n 0) (l 0) (t 0)) (((z)) ((l) (n (r l))) ((f))))
(declare-fun x () l)
(assert (and (not (= l (r x))) (not ((_ is n) (r x)))))
(check-sat)
