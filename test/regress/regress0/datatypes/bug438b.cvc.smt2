; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-datatypes ((list 1)) ((par (T)((cons (car T) (cdr (list T))) (nil)))))
(declare-fun x () (list Real))
(assert (= x (cons 1.0 (as nil (list Real)))))
(assert (= x ((as cons (list Real)) 1.0 (as nil (list Real)))))
(check-sat)
