; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((List 0)) (((cons (car Bool) (cdr List)) (nil))))
(declare-fun x () List)
(assert (not (= x nil)))
(check-sat)
