; COMMAND-LINE:
; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun A () (Bag Int))
(declare-fun a () Int)
(assert (not (= A (as bag.empty (Bag Int)))))
(assert (= (bag.choose A) 10))
(assert (= (bag.choose A) a))
(check-sat)
