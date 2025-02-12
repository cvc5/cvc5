; COMMAND-LINE: --mbqi --mbqi-enum
; EXPECT: sat
(set-logic HO_ALL)
(declare-const P (-> Int Bool))
(declare-const f (-> (-> Int Bool) Int))
(assert (forall ((x (-> Int Bool))) (P (f x))))
(check-sat)
