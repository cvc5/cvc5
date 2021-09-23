; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((single_ctor 0)) (((foo (bar Real)))))
(declare-datatypes ((double_ctor 0)) (((foo2 (bar2 Real)) (baz))))
(declare-fun x () single_ctor)
(declare-fun y () double_ctor)
(check-sat-assuming ( (not (let ((_let_1 0.0)) (and ((_ is foo) x) (= (bar2 (foo2 _let_1)) _let_1)))) ))
