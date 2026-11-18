; EXPECT: sat
(set-logic ALL)
(declare-datatypes ((T 1)) ((par (a) ((|C,| (|fst,| a) (|snd,| a)) (|D,|)))))
(declare-const s (T Int))
(assert ((_ is |C,|) s))
(assert (not ((_ is |D,|) s)))
(check-sat)
