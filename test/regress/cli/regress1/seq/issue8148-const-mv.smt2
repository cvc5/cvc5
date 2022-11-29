; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(set-option :re-elim agg)
(declare-fun e!0 () (Seq Bool))
(assert (= e!0 seq.empty))
(assert (seq.nth e!0 0))
(check-sat)
