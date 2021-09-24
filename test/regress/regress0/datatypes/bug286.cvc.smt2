; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((foo 0)) (((f (i Int)))))
(declare-fun x () foo)
(declare-fun y () Int)
(check-sat-assuming ( (not (= x (f y))) ))
