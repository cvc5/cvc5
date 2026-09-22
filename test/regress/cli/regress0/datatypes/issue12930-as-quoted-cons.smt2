; EXPECT: sat
(set-logic ALL)
(declare-datatypes ((T 1)) ((par (a) ((|C,| (|fst| a) (|snd| a))))))
(declare-const s (T Int))
(assert (= s ((as |C,| (T Int)) 1 2)))
(check-sat)
