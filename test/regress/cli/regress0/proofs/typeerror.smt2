; COMMAND-LINE: --proof-elim-subtypes
; EXPECT: unsat
(set-logic AUFLIRA)
(assert (! (not (exists ((?v0 Int)) (forall ((?v1 Int) (?v2 Real)) (=> (and (< 0 ?v1) (< 0.0 ?v2)) (< (- 1) ?v1))))) :named a0))
(check-sat)
