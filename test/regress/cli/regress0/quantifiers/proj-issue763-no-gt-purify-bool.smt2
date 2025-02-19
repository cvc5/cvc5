; COMMAND-LINE: --mbqi
; EXPECT: sat
(set-logic ALL)
(declare-const x5 (Seq Bool))
(declare-const x (Array Bool Bool))
(assert (not (select x (exists ((_x (Seq Bool))) (forall ((x (Array Bool Bool))) (select x (seq.prefixof x5 _x)))))))
(check-sat)
