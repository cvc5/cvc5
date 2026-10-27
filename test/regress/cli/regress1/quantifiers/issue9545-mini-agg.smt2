; COMMAND-LINE: --miniscope-quant=agg
; EXPECT: unknown
(set-logic ALL)
(assert (forall ((r Int) (r8 Int) (v (Array Int (Array Int Real)))) (or (= r r8) (= (select (select v 0) 0) (select (select v 0) r8)))))
(check-sat)
