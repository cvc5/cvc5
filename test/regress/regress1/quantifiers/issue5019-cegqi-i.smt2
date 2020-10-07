; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
(set-logic BV)
(declare-const v4 Bool)
(assert (forall ((q0 Bool) (q1 Bool)) (xor true true q1 v4 q1 true true true true true true)))
(push 1)
(check-sat)
(pop 1)
(check-sat)
