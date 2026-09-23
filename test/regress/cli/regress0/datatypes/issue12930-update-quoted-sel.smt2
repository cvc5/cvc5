; EXPECT: unsat
(set-logic ALL)
(declare-datatypes ((T 1)) ((par (a) ((|C,| (|fst,| a) (|snd,| a))))))
(declare-const s (T Int))
(assert (not (= (|fst,| ((_ update |fst,|) s 3)) 3)))
(check-sat)
