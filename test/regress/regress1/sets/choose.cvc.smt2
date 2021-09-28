; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun A () (Set Int))
(declare-fun a () Int)
(assert (not (= A (as emptyset (Set Int)))))
(assert (= (choose A) 10))
(assert (= (choose A) a))
(check-sat)
