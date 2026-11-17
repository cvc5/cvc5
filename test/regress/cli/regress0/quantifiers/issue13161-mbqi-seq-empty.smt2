; COMMAND-LINE: --mbqi
; EXPECT: unknown
(set-logic ALL)
(declare-fun g ((Seq Int)) Int)
(assert (forall ((a (Seq Int))) (= (g a) (seq.len a))))
(check-sat)
