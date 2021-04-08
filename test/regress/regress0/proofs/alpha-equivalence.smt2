; COMMAND-LINE:
; EXIT: 0
; SCRUBBER: grep -v -E '.*'
(set-logic AUFLIA)
(set-option :produce-proofs true)
(declare-sort A$ 0)
(declare-fun p$ (A$) Bool)
(assert (exists ((?v0 A$)) (p$ ?v0)))
(assert (forall ((?v0 A$)) (not (p$ ?v0))))
(assert (not false))
(check-sat)
(get-proof)
